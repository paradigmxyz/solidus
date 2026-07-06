#!/usr/bin/env python3
"""Frozen import-closure checker for the Solidus Arena freeze cone.

Reads a manifest of frozen repo files and verifies that every frozen module
imports ONLY:

  * another file listed in the manifest, or
  * a trusted-external package (EvmYul / Lean / Init / Std / Batteries /
    Mathlib and the other pinned lake dependencies), or
  * a module explicitly declared trusted in the manifest via an `#allow:`
    directive (used to record the residual, definition-level-trust gaps where
    a hash-frozen semantic file still imports mutable compiler machinery that
    its frozen *definitions* do not reference).

Exit code 0 = closed (green); 1 = a frozen file reaches an unlisted mutable
module; 2 = manifest / usage error.

Manifest format (one entry per line, `#` starts a comment):

    EvmCompiler/Solidus/Bridge.lean            # a frozen file (repo-relative)
    #allow: EvmCompiler.Assembly.PrimSemantics # trusted mutable import
    #trusted: EvmYul                           # extra trusted package prefix
"""
import sys
import os
import re

DEFAULT_TRUSTED_PREFIXES = [
    "EvmYul", "Lean", "Init", "Std", "Batteries", "Mathlib", "Qq", "Aesop",
    "Cli", "ImportGraph", "LeanSearchClient", "Plausible", "ProofWidgets",
]

IMPORT_RE = re.compile(r"^\s*import\s+([A-Za-z0-9_.]+)")


def module_of(path):
    """EvmCompiler/Solidus/Bridge.lean -> EvmCompiler.Solidus.Bridge"""
    p = path
    if p.endswith(".lean"):
        p = p[:-5]
    return p.replace("/", ".")


def path_of(module):
    return module.replace(".", "/") + ".lean"


def main():
    if len(sys.argv) != 2:
        sys.stderr.write("usage: check_frozen_closure.py <manifest>\n")
        return 2
    manifest = sys.argv[1]
    root = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
    frozen_files = []
    frozen_modules = set()
    allow = set()
    trusted_prefixes = list(DEFAULT_TRUSTED_PREFIXES)

    with open(manifest) as f:
        for raw in f:
            line = raw.strip()
            if not line:
                continue
            if line.startswith("#allow:"):
                allow.add(line[len("#allow:"):].strip())
                continue
            if line.startswith("#trusted:"):
                trusted_prefixes.append(line[len("#trusted:"):].strip())
                continue
            if line.startswith("#"):
                continue
            # Strip trailing inline comment on a file entry.
            entry = line.split("#", 1)[0].strip()
            if not entry:
                continue
            frozen_files.append(entry)
            frozen_modules.add(module_of(entry))

    def is_trusted(mod):
        head = mod.split(".", 1)[0]
        return head in trusted_prefixes

    ok = True
    checked = 0
    for rel in frozen_files:
        full = os.path.join(root, rel)
        if not os.path.exists(full):
            # Non-.lean pins (lean-toolchain, lake-manifest.json) are frozen by
            # hash but carry no imports; anything else missing is an error.
            if rel.endswith(".lean"):
                sys.stderr.write("MISSING frozen file: %s\n" % rel)
                ok = False
            continue
        if not rel.endswith(".lean"):
            continue
        checked += 1
        with open(full) as fh:
            for ln in fh:
                m = IMPORT_RE.match(ln)
                if not m:
                    # imports are only at the top; stop at first non-import,
                    # non-comment, non-blank line.
                    s = ln.strip()
                    if s and not s.startswith("--") and not s.startswith("/-") \
                            and not s.startswith("import"):
                        break
                    continue
                mod = m.group(1)
                if mod in frozen_modules:
                    continue
                if is_trusted(mod):
                    continue
                if mod in allow:
                    continue
                sys.stderr.write(
                    "CLOSURE VIOLATION: %s imports unlisted mutable module %s\n"
                    % (rel, mod))
                ok = False

    if ok:
        print("frozen closure OK: %d .lean files checked, %d frozen modules, "
              "%d allowed mutable imports" %
              (checked, len(frozen_modules), len(allow)))
        return 0
    return 1


if __name__ == "__main__":
    sys.exit(main())
