#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Acme JSONPath Coq → OCaml end-to-end runner with a Tkinter GUI.

What this tool does:
  1) Takes a Coq .v file (your JSONPath semantics + extraction block)
  2) Runs 'coqc' to produce 'jsonpath_exec.ml'
  3) Creates a minimal Dune project (library + harness)
  4) Builds with 'dune'
  5) Lets you run queries on either built-in datasets (company/acme) or your own JSON file
  6) Displays results as lines: <path> => <value>

Prereqs you should have installed in your shell:
  - coqc (Coq)
  - dune (OCaml build system)
  - opam packages: num, yojson
  - python modules: tkinter (stdlib), optionally tkinterdnd2 for drag-and-drop
"""

import os
import sys
import shutil
import subprocess
import tempfile
from pathlib import Path
import textwrap

import tkinter as tk
from tkinter import filedialog, messagebox
from tkinter.scrolledtext import ScrolledText

# Try optional drag-and-drop support
DND_AVAILABLE = False
try:
    from tkinterdnd2 import DND_FILES, TkinterDnD
    DND_AVAILABLE = True
except Exception:
    DND_AVAILABLE = False


# ------------------------- Harness OCaml code -------------------------

OCAML_MAIN_ML = r'''(* bin/main.ml *)
open Printf
open Jsonpath_exec
open Big_int

let string_of_z (z : Big_int.big_int) = Big_int.string_of_big_int z

let string_of_step = function
  | JSON.SName s  -> "." ^ s
  | JSON.SIndex i -> "[" ^ string_of_z i ^ "]"

let string_of_path (p : JSON.path) =
  String.concat "" (List.map string_of_step p)

let string_of_value =
  let rec go = function
    | JSON.JNull       -> "null"
    | JSON.JBool b     -> if b then "true" else "false"
    | JSON.JStr s      -> "\"" ^ String.escaped s ^ "\""
    | JSON.JNum _q     -> "<num>"
    | JSON.JArr xs     -> "[" ^ (String.concat ", " (List.map go xs)) ^ "]"
    | JSON.JObject kvs ->
        let fields =
          List.map (fun (k,v) -> "\"" ^ String.escaped k ^ "\": " ^ go v) kvs in
        "{ " ^ String.concat ", " fields ^ " }"
  in go

let print_nodes (nodes : JSON.node list) =
  List.iter (fun (p,v) ->
    printf "%s => %s\n" (string_of_path p) (string_of_value v)
  ) nodes

(* Convert decimal string to JSON.JNum with exact rational *)
let jnum_of_decimal_string (s : string) : JSON.value =
  let len = String.length s in
  let idx = ref 0 in
  let get i = if i < len then s.[i] else '\000' in
  let is_digit c = '0' <= c && c <= '9' in
  let sign =
    match get !idx with
    | '-' -> incr idx; -1
    | '+' -> incr idx;  1
    | _   -> 1
  in
  let digits_from i =
    let j = ref i in
    while !j < len && is_digit (get !j) do incr j done;
    (String.sub s i (!j - i), !j)
  in
  let int_part, i1 = digits_from !idx in
  idx := i1;
  let frac_part =
    if !idx < len && get !idx = '.' then (
      incr idx;
      let ds, j = digits_from !idx in
      idx := j; ds
    ) else ""
  in
  let exp_val =
    if !idx < len && (get !idx = 'e' || get !idx = 'E') then (
      incr idx;
      let esign =
        if !idx < len && (get !idx = '+' || get !idx = '-') then
          let c = get !idx in incr idx; if c = '-' then -1 else 1
        else 1
      in
      let estr, j = digits_from !idx in
      idx := j;
      let e = if estr = "" then 0 else int_of_string estr in
      esign * e
    ) else 0
  in
  let pow10 n = Big_int.power_int_positive_int 10 (abs n) in
  let bi s = if s = "" then Big_int.zero_big_int else Big_int.big_int_of_string s in
  let f = String.length frac_part in
  let int_bi  = bi (if int_part = "" then "0" else int_part) in
  let frac_bi = bi (if frac_part = "" then "0" else frac_part) in
  let base    = pow10 f in
  let num0    = Big_int.add_big_int (Big_int.mult_big_int int_bi base) frac_bi in
  let num0    = if sign < 0 then Big_int.minus_big_int num0 else num0 in
  let den0    = if f = 0 then Big_int.unit_big_int else base in
  let num, den =
    if exp_val = 0 then num0, den0
    else if exp_val > 0 then
      Big_int.mult_big_int num0 (pow10 exp_val), den0
    else
      let p = pow10 exp_val in
      num0, Big_int.mult_big_int den0 p
  in
  let den = if Big_int.sign_big_int den <= 0 then Big_int.unit_big_int else den in
  let q = QArith_base.Qmake num den in
  JSON.JNum q

let rec of_yojson (j : Yojson.Safe.t) : JSON.value =
  match j with
  | `Null       -> JSON.JNull
  | `Bool b     -> JSON.JBool b
  | `String s   -> JSON.JStr s
  | `Int i      -> JSON.JNum (QArith_base.inject_Z (Big_int.big_int_of_int i))
  | `Intlit s   -> jnum_of_decimal_string s
  | `Float f    -> jnum_of_decimal_string (Printf.sprintf "%.17g" f)
  | `Floatlit s -> jnum_of_decimal_string s
  | `List xs    -> JSON.JArr (List.map of_yojson xs)
  | `Assoc kvs  -> JSON.JObject (List.map (fun (k,v) -> (k, of_yojson v)) kvs)

let desc_name (name : string) : JSONPath.query =
  JSONPath.Query [ JSONPath.Desc [ JSONPath.SelName name ] ]

let child_name (name : string) : JSONPath.query =
  JSONPath.Query [ JSONPath.Child [ JSONPath.SelName name ] ]

let child_index (n : int) : JSONPath.query =
  JSONPath.Query [ JSONPath.Child [ JSONPath.SelIndex (Big_int.big_int_of_int n) ] ]

let wildcard_desc : JSONPath.query =
  JSONPath.Query [ JSONPath.Desc [ JSONPath.SelWildcard ] ]

type source =
  | Built_in of [ `Acme | `Company ]
  | From_file of string

type qkind =
  | QDescName of string
  | QChildName of string
  | QChildIndex of int
  | QWildcardDesc

let run (src:source) (qk:qkind) =
  let q =
    match qk with
    | QDescName n   -> desc_name n
    | QChildName n  -> child_name n
    | QChildIndex i -> child_index i
    | QWildcardDesc -> wildcard_desc
  in
  let json_value =
    match src with
    | Built_in `Acme    -> acme_db_json
    | Built_in `Company -> company_json
    | From_file path ->
        let yo = Yojson.Safe.from_file path in
        of_yojson yo
  in
  let results = Exec.eval_exec q json_value in
  print_nodes results

let usage () =
  eprintf "Usage: acme-jsonpath [--demo acme|company | --file data.json] [--desc-name N | --child-name N | --child-index I | --wildcard-desc]\n%!"

let () =
  let src = ref None in
  let q   = ref None in
  let set_demo s =
    match String.lowercase_ascii s with
    | "acme"    -> src := Some (Built_in `Acme)
    | "company" -> src := Some (Built_in `Company)
    | _         -> eprintf "Unknown demo: %s\n" s; exit 2
  in
  let set_file f = src := Some (From_file f) in
  let set_desc n = q := Some (QDescName n) in
  let set_child n = q := Some (QChildName n) in
  let set_index i = q := Some (QChildIndex (int_of_string i)) in
  let set_wild () = q := Some QWildcardDesc in
  let speclist = [
    ("--demo", Arg.String set_demo,      "Use built-in dataset: acme | company");
    ("--file", Arg.String set_file,      "Use external JSON file");
    ("--desc-name", Arg.String set_desc, "Query $..NAME");
    ("--child-name", Arg.String set_child, "Query .NAME at root");
    ("--child-index", Arg.String set_index, "Query [INDEX] at root (array)");
    ("--wildcard-desc", Arg.Unit set_wild, "Query $..*");
  ] in
  Arg.parse speclist (fun _ -> ()) "acme-jsonpath";
  match !src, !q with
  | Some s, Some k -> run s k
  | _ -> usage (); exit 2
'''

DUNE_PROJECT = """(lang dune 3.13)
(name acme_jsonpath)
"""

LIB_DUNE = """(library
 (name jsonpath)
 (modules jsonpath_exec)
 (libraries num))
"""

BIN_DUNE = """(executable
 (name main)
 (public_name acme-jsonpath)
 (libraries jsonpath yojson num))
"""


# ------------------------- Helpers -------------------------

def which_or_hint(cmd: str) -> bool:
    return shutil.which(cmd) is not None

def run_cmd(args, cwd=None):
    """Run a subprocess and return (rc, stdout, stderr)."""
    p = subprocess.run(
        args,
        cwd=cwd,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        shell=False
    )
    return p.returncode, p.stdout, p.stderr


# ------------------------- Core Build Logic -------------------------

class BuildContext:
    def __init__(self):
        self.coq_file: Path | None = None
        self.coq_dir: Path | None = None
        self.extracted_ml: Path | None = None
        self.work_root: Path | None = None
        self.exe_path: Path | None = None

    def reset(self):
        self.extracted_ml = None
        self.work_root = None
        self.exe_path = None


def build_engine(ctx: BuildContext, log_cb=print):
    """
    1) Run 'coqc <file.v>' to produce jsonpath_exec.ml (as per extraction block)
    2) Create a dune project with lib/jsonpath_exec.ml and bin/main.ml
    3) dune build
    """
    if ctx.coq_file is None:
        raise RuntimeError("No Coq .v file selected.")

    if not which_or_hint("coqc"):
        raise RuntimeError("coqc not found on PATH. Install Coq or update PATH.")

    if not which_or_hint("dune"):
        raise RuntimeError("dune not found on PATH. Install dune (e.g., `opam install dune`).")

    coq_dir = ctx.coq_file.parent
    log_cb(f"Running coqc in: {coq_dir}")
    rc, out, err = run_cmd(["coqc", ctx.coq_file.name], cwd=str(coq_dir))
    log_cb(out)
    if rc != 0:
        raise RuntimeError(f"coqc failed:\n{err}")

    # After coqc, the extraction should produce jsonpath_exec.ml in coq_dir
    extracted = coq_dir / "jsonpath_exec.ml"
    if not extracted.exists():
        raise RuntimeError(
            "Extraction did not produce jsonpath_exec.ml. "
            "Ensure your .v file ends with the extraction block."
        )
    ctx.extracted_ml = extracted

    # Prepare a work root (next to coq file, in _acme_jsonpath_build)
    work_root = coq_dir / "_acme_jsonpath_build"
    work_root.mkdir(exist_ok=True)
    (work_root / "lib").mkdir(exist_ok=True, parents=True)
    (work_root / "bin").mkdir(exist_ok=True, parents=True)
    ctx.work_root = work_root

    # Write dune files
    (work_root / "dune-project").write_text(DUNE_PROJECT, encoding="utf-8")
    (work_root / "lib" / "dune").write_text(LIB_DUNE, encoding="utf-8")
    (work_root / "bin" / "dune").write_text(BIN_DUNE, encoding="utf-8")

    # Copy extracted ML
    shutil.copy2(str(extracted), str(work_root / "lib" / "jsonpath_exec.ml"))

    # Write harness main.ml
    (work_root / "bin" / "main.ml").write_text(OCAML_MAIN_ML, encoding="utf-8")

    # dune build
    log_cb(f"Running dune build in: {work_root}")
    rc, out, err = run_cmd(["dune", "build"], cwd=str(work_root))
    log_cb(out)
    if rc != 0:
        raise RuntimeError(
            "dune build failed. You likely need `opam install num yojson`.\n" + err
        )

    # Determine executable path
    if sys.platform.startswith("win"):
        exe_rel = Path("_build") / "default" / "bin" / "main.exe"
    else:
        exe_rel = Path("_build") / "default" / "bin" / "main"
    exe_path = work_root / exe_rel
    if not exe_path.exists():
        raise RuntimeError("Built executable not found at: " + str(exe_path))
    ctx.exe_path = exe_path

    log_cb("Build success: " + str(exe_path))


def run_query(ctx: BuildContext, source_kind: str, source_value: str, query_kind: str, query_value: str, log_cb=print):
    """
    Execute the built CLI:
      source_kind: 'demo' or 'file'
      source_value: 'acme'|'company' or path to file
      query_kind: 'desc-name'|'child-name'|'child-index'|'wildcard-desc'
      query_value: name or index (string) or '' for wildcard
    """
    if ctx.exe_path is None:
        raise RuntimeError("Engine not built yet.")

    args = [str(ctx.exe_path)]
    # source
    if source_kind == "demo":
        if source_value not in ("acme", "company"):
            raise RuntimeError("Demo must be 'acme' or 'company'.")
        args += ["--demo", source_value]
    elif source_kind == "file":
        p = Path(source_value)
        if not p.exists():
            raise RuntimeError("JSON file does not exist: " + source_value)
        args += ["--file", str(p)]
    else:
        raise RuntimeError("Unknown source_kind: " + source_kind)

    # query
    if query_kind == "desc-name":
        if not query_value:
            raise RuntimeError("desc-name requires a NAME.")
        args += ["--desc-name", query_value]
    elif query_kind == "child-name":
        if not query_value:
            raise RuntimeError("child-name requires a NAME.")
        args += ["--child-name", query_value]
    elif query_kind == "child-index":
        if not query_value:
            raise RuntimeError("child-index requires an integer.")
        args += ["--child-index", str(int(query_value))]
    elif query_kind == "wildcard-desc":
        args += ["--wildcard-desc"]
    else:
        raise RuntimeError("Unknown query_kind: " + query_kind)

    log_cb("Running: " + " ".join(args))
    rc, out, err = run_cmd(args, cwd=str(ctx.work_root))
    if rc != 0:
        raise RuntimeError("Query execution failed:\n" + err)
    return out


# ------------------------- GUI -------------------------

class App:
    def __init__(self, root):
        self.root = root
        root.title("Acme JSONPath (Coq→OCaml) Runner")

        self.ctx = BuildContext()

        # --- Coq file selection
        f_top = tk.LabelFrame(root, text="1) Coq .v file (with extraction block)")
        f_top.pack(fill="x", padx=8, pady=6)

        self.coq_entry = tk.Entry(f_top)
        self.coq_entry.pack(side="left", fill="x", expand=True, padx=6, pady=6)
        tk.Button(f_top, text="Browse…", command=self.browse_coq).pack(side="left", padx=6)
        tk.Button(f_top, text="Build Engine", command=self.on_build).pack(side="left", padx=6)

        # --- Source selection
        f_src = tk.LabelFrame(root, text="2) Data source")
        f_src.pack(fill="x", padx=8, pady=6)

        self.src_var = tk.StringVar(value="demo")
        rb1 = tk.Radiobutton(f_src, text="Built-in: acme", variable=self.src_var, value="demo", command=self.on_src_change)
        rb2 = tk.Radiobutton(f_src, text="External JSON file", variable=self.src_var, value="file", command=self.on_src_change)
        rb1.grid(row=0, column=0, sticky="w", padx=6, pady=4)
        rb2.grid(row=0, column=1, sticky="w", padx=6, pady=4)

        self.demo_var = tk.StringVar(value="acme")
        tk.OptionMenu(f_src, self.demo_var, "acme", "company").grid(row=0, column=2, padx=6)

        self.file_entry = tk.Entry(f_src, state="disabled", width=50)
        self.file_entry.grid(row=1, column=0, columnspan=3, sticky="we", padx=6, pady=6)
        tk.Button(f_src, text="Browse JSON…", command=self.browse_json, state="disabled").grid(row=1, column=3, padx=6)

        # optional drag-and-drop
        if DND_AVAILABLE:
            drop_label = tk.Label(f_src, text="Drag & drop JSON here", relief="groove")
            drop_label.grid(row=2, column=0, columnspan=4, sticky="we", padx=6, pady=6)
            drop_label.drop_target_register(DND_FILES)
            drop_label.dnd_bind('<<Drop>>', self.on_drop_json)
        else:
            tk.Label(f_src, text="(Install 'tkinterdnd2' for drag‑and‑drop)").grid(row=2, column=0, columnspan=4, sticky="w", padx=6)

        f_src.grid_columnconfigure(0, weight=1)
        f_src.grid_columnconfigure(1, weight=0)
        f_src.grid_columnconfigure(2, weight=0)
        f_src.grid_columnconfigure(3, weight=0)

        # --- Query selection
        f_q = tk.LabelFrame(root, text="3) Query")
        f_q.pack(fill="x", padx=8, pady=6)

        self.q_var = tk.StringVar(value="desc-name")
        tk.Radiobutton(f_q, text="$..NAME (desc-name)", variable=self.q_var, value="desc-name", command=self.on_q_change).grid(row=0, column=0, sticky="w", padx=6, pady=4)
        tk.Radiobutton(f_q, text=".NAME (child-name)", variable=self.q_var, value="child-name", command=self.on_q_change).grid(row=0, column=1, sticky="w", padx=6, pady=4)
        tk.Radiobutton(f_q, text="[INDEX] (child-index)", variable=self.q_var, value="child-index", command=self.on_q_change).grid(row=0, column=2, sticky="w", padx=6, pady=4)
        tk.Radiobutton(f_q, text="$..* (wildcard-desc)", variable=self.q_var, value="wildcard-desc", command=self.on_q_change).grid(row=0, column=3, sticky="w", padx=6, pady=4)

        tk.Label(f_q, text="Name / Index:").grid(row=1, column=0, sticky="e", padx=6)
        self.q_value_entry = tk.Entry(f_q)
        self.q_value_entry.grid(row=1, column=1, columnspan=3, sticky="we", padx=6, pady=6)

        f_q.grid_columnconfigure(1, weight=1)
        f_q.grid_columnconfigure(2, weight=0)
        f_q.grid_columnconfigure(3, weight=0)

        # --- Run & output
        f_run = tk.LabelFrame(root, text="4) Run & Output")
        f_run.pack(fill="both", expand=True, padx=8, pady=6)

        tk.Button(f_run, text="Run Query", command=self.on_run).pack(anchor="w", padx=6, pady=4)

        self.out = ScrolledText(f_run, height=20)
        self.out.pack(fill="both", expand=True, padx=6, pady=6)

        # status bar
        self.status = tk.StringVar(value="Ready")
        tk.Label(root, textvariable=self.status, anchor="w").pack(fill="x", padx=8, pady=4)

        # if TkinterDnD, need to use its root class; otherwise normal tk.Tk
        if DND_AVAILABLE and isinstance(root, TkinterDnD.Tk):
            pass

    def log(self, msg: str):
        self.out.insert("end", msg + "\n")
        self.out.see("end")
        self.status.set(msg)
        self.root.update_idletasks()

    def browse_coq(self):
        p = filedialog.askopenfilename(
            title="Select Coq .v file",
            filetypes=[("Coq files", "*.v"), ("All files", "*.*")]
        )
        if p:
            self.coq_entry.delete(0, "end")
            self.coq_entry.insert(0, p)
            self.ctx.coq_file = Path(p)
            self.ctx.coq_dir = self.ctx.coq_file.parent

    def on_build(self):
        try:
            if not self.coq_entry.get().strip():
                messagebox.showerror("Missing", "Please select a Coq .v file first.")
                return
            self.ctx.coq_file = Path(self.coq_entry.get().strip())
            self.ctx.reset()
            self.log("Building engine...")
            build_engine(self.ctx, log_cb=self.log)
            self.log("Build completed.")
        except Exception as e:
            messagebox.showerror("Build failed", str(e))
            self.log("Build failed.")

    def on_src_change(self):
        mode = self.src_var.get()
        if mode == "demo":
            self.file_entry.config(state="disabled")
        else:
            self.file_entry.config(state="normal")

    def browse_json(self):
        p = filedialog.askopenfilename(
            title="Select JSON file",
            filetypes=[("JSON files", "*.json;*.jsonl;*.ndjson"), ("All files", "*.*")]
        )
        if p:
            self.file_entry.delete(0, "end")
            self.file_entry.insert(0, p)

    def on_drop_json(self, event):
        if self.src_var.get() != "file":
            self.src_var.set("file")
            self.on_src_change()
        # event.data may contain braces and spaces; normalize
        raw = event.data.strip()
        # The DND_FILES format may be a list; take the first path
        if raw.startswith("{") and raw.endswith("}"):
            raw = raw[1:-1]
        path = raw.split()[0]
        self.file_entry.delete(0, "end")
        self.file_entry.insert(0, path)

    def on_q_change(self):
        kind = self.q_var.get()
        if kind == "wildcard-desc":
            self.q_value_entry.delete(0, "end")
            self.q_value_entry.config(state="disabled")
        else:
            self.q_value_entry.config(state="normal")

    def on_run(self):
        try:
            if self.ctx.exe_path is None:
                messagebox.showerror("Not built", "Please build the engine first.")
                return

            # source
            if self.src_var.get() == "demo":
                source_kind = "demo"
                source_value = self.demo_var.get()
            else:
                source_kind = "file"
                source_value = self.file_entry.get().strip()
                if not source_value:
                    messagebox.showerror("Missing", "Please choose a JSON file.")
                    return

            # query
            query_kind = self.q_var.get()
            query_value = self.q_value_entry.get().strip()

            self.log("Executing query...")
            out = run_query(self.ctx, source_kind, source_value, query_kind, query_value, log_cb=self.log)
            self.log("=== RESULTS ===")
            self.log(out.rstrip("\n"))
            self.log("===============")
        except Exception as e:
            messagebox.showerror("Run failed", str(e))
            self.log("Run failed.")


def main():
    if DND_AVAILABLE:
        root = TkinterDnD.Tk()
    else:
        root = tk.Tk()
    app = App(root)
    root.minsize(800, 600)
    root.mainloop()


if __name__ == "__main__":
    main()
