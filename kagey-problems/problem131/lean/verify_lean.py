"""Build the Problem 131 Lean libraries and check the axioms of every theorem.

For each requested library (default: every one of PaperA, PaperB, PaperC, PaperD
whose root file exists in this folder) the script

1. collects the modules imported by the root file `<Lib>.lean`, and every
   `theorem` and `lemma` declared in them,
2. runs `lake build <Lib>` in a Lake workspace whose lakefile has
   `lean_lib <Lib>` with `srcDir` equal to this folder (a workspace inside
   OneDrive is refused, since Lake writes many files into `.lake`),
3. writes a temporary Lean file inside the workspace that imports the library,
   runs `#print axioms` on each declaration, and lists every theorem the
   library actually contains (so a declaration missed by the parser is caught),
4. checks that the only axioms are propext, Classical.choice and Quot.sound,
5. writes build-log.txt and verification-manifest.json in this folder.

Entries for libraries that were not requested are kept in both output files.

Examples (run from this folder):
    python -B verify_lean.py                    # workspaces ~/lean-work/paperA, ...
    python -B verify_lean.py PaperB
    python -B verify_lean.py --workspace .      # use the lakefile in this folder
    python -B verify_lean.py --workspace D:/lean/{name}

In --workspace, `{lib}` is replaced by the library name (PaperA) and `{name}`
by the same name with a lower-case first letter (paperA).
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import threading
import tomllib
from datetime import datetime, timezone
from pathlib import Path

BASE = Path(__file__).resolve().parent
LIBS = ['PaperA', 'PaperB', 'PaperC', 'PaperD']
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
LOG_FILE = BASE / 'build-log.txt'
MANIFEST_FILE = BASE / 'verification-manifest.json'
ANSI = re.compile(r'\x1b\[[0-9;?]*[A-Za-z]')


class CheckFailed(Exception):
    pass


# ---------------------------------------------------------------- arguments

def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(
        description='Build the Problem 131 Lean libraries and check their axioms.')
    p.add_argument('libs', nargs='*', metavar='LIB',
                   help='libraries to check (default: all of PaperA..PaperD that exist)')
    p.add_argument('--workspace', default=str(Path.home() / 'lean-work' / '{name}'),
                   help='Lake workspace, or a pattern with {lib} or {name} '
                        '(default: ~/lean-work/{name}). Use "." for this folder.')
    p.add_argument('--toolchain', default=None,
                   help='directory containing lean and lake (default: the elan '
                        'toolchain named in lean-toolchain, then PATH)')
    p.add_argument('--lean', default=None,
                   help='path to the lean executable, whose folder is used as --toolchain')
    p.add_argument('--build-timeout', type=float, default=4 * 3600,
                   help='seconds allowed for lake build (default 4 hours)')
    p.add_argument('--check-timeout', type=float, default=3600,
                   help='seconds allowed for the axiom check (default 1 hour)')
    args = p.parse_args()
    if not args.libs:
        args.libs = [lib for lib in LIBS if (BASE / f'{lib}.lean').is_file()]
    for lib in args.libs:
        if lib not in LIBS:
            p.error(f'unknown library {lib} (expected one of {", ".join(LIBS)})')
        if not (BASE / f'{lib}.lean').is_file():
            p.error(f'{lib}.lean does not exist in {BASE}')
    if not args.libs:
        p.error('no library root files found')
    if args.lean and not args.toolchain:
        args.toolchain = str(Path(args.lean).expanduser().resolve().parent)
    return args


# ---------------------------------------------------------------- tools

def find_tools(toolchain: str | None) -> tuple[str, str, dict[str, str]]:
    dirs: list[Path] = []
    if toolchain:
        dirs.append(Path(toolchain).expanduser())
    else:
        spec = (BASE / 'lean-toolchain').read_text(encoding='utf-8').strip()
        elan_home = Path(os.environ.get('ELAN_HOME', Path.home() / '.elan'))
        candidate = elan_home / 'toolchains' / spec.replace('/', '--').replace(':', '---') / 'bin'
        if candidate.is_dir():
            dirs.append(candidate)
    path = os.pathsep.join([str(d) for d in dirs] + [os.environ.get('PATH', '')])
    lake = shutil.which('lake', path=path)
    lean = shutil.which('lean', path=path)
    if not lake or not lean:
        sys.exit('Cannot find lake and lean. Install elan or pass --toolchain.')
    return lake, lean, dict(os.environ, PATH=path)


def run_streaming(cmd: list[str], cwd: Path, env: dict[str, str], timeout: float) -> tuple[int, str]:
    """Run a command, echo its output, and return (exit code, output)."""
    proc = subprocess.Popen(cmd, cwd=cwd, env=env, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, text=True, encoding='utf-8',
                            errors='replace')
    lines: list[str] = []

    def reader() -> None:
        assert proc.stdout is not None
        for line in proc.stdout:
            line = ANSI.sub('', line)
            lines.append(line)
            if not line.startswith('@@THEOREM '):
                print('   ' + line, end='', flush=True)

    thread = threading.Thread(target=reader, daemon=True)
    thread.start()
    try:
        code = proc.wait(timeout=timeout)
    except subprocess.TimeoutExpired:
        proc.kill()
        raise CheckFailed(f'{Path(cmd[0]).name} {" ".join(cmd[1:])} timed out after {timeout:.0f} s')
    thread.join()
    return code, ''.join(lines)


# ---------------------------------------------------------------- workspace

def same_path(a: Path, b: Path) -> bool:
    return os.path.normcase(str(a.resolve())) == os.path.normcase(str(b.resolve()))


def resolve_workspace(lib: str, pattern: str) -> Path:
    name = lib[0].lower() + lib[1:]
    ws = Path(os.path.expanduser(pattern.format(lib=lib, name=name))).resolve()
    if 'onedrive' in str(ws).lower():
        raise CheckFailed(f'{ws} is inside OneDrive. Lake writes thousands of files into .lake, '
                          'so use a workspace outside the synced folder.')
    if not ws.is_dir():
        raise CheckFailed(f'workspace {ws} does not exist')
    toml = ws / 'lakefile.toml'
    if toml.is_file():
        config = tomllib.loads(toml.read_text(encoding='utf-8'))
        libs = {entry.get('name'): entry for entry in config.get('lean_lib', [])}
        if lib not in libs:
            raise CheckFailed(f'{toml} has no lean_lib {lib}')
        src = ws / libs[lib].get('srcDir', '.')
        if not same_path(src, BASE):
            raise CheckFailed(f'lean_lib {lib} in {toml} reads {src.resolve()}, not {BASE}')
    elif (ws / 'lakefile.lean').is_file():
        print(f'   note: {ws / "lakefile.lean"} is not parsed; assuming it builds {BASE}')
    else:
        raise CheckFailed(f'{ws} has no lakefile')
    ours = (BASE / 'lean-toolchain').read_text(encoding='utf-8').strip()
    theirs_file = ws / 'lean-toolchain'
    if theirs_file.is_file() and theirs_file.read_text(encoding='utf-8').strip() != ours:
        raise CheckFailed(f'{theirs_file} does not say {ours}')
    return ws


def mathlib_rev(ws: Path) -> str | None:
    manifest = ws / 'lake-manifest.json'
    if not manifest.is_file():
        return None
    data = json.loads(manifest.read_text(encoding='utf-8'))
    for package in data.get('packages', []):
        if package.get('name') == 'mathlib':
            return package.get('rev')
    return None


# ---------------------------------------------------------------- sources

def strip_comments(src: str) -> str:
    """Remove Lean comments and string literals, keeping line breaks."""
    out: list[str] = []
    i, n, depth = 0, len(src), 0
    while i < n:
        if depth:
            if src.startswith('/-', i):
                depth += 1
                i += 2
            elif src.startswith('-/', i):
                depth -= 1
                i += 2
            else:
                if src[i] == '\n':
                    out.append('\n')
                i += 1
        elif src.startswith('/-', i):
            depth = 1
            i += 2
        elif src.startswith('--', i):
            j = src.find('\n', i)
            i = n if j < 0 else j
        elif src[i] == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == '\\' else 1
            out.append('""' + '\n' * src.count('\n', i, j))
            i = j + 1
        else:
            out.append(src[i])
            i += 1
    return ''.join(out)


IMPORT_RE = re.compile(r'^\s*(?:public\s+|private\s+)?(?:meta\s+)?import\s+(?:all\s+)?(.+)$')
DECL_RE = re.compile(
    r'^\s*(?:@\[[^\]]*\]\s*)*'
    r'((?:(?:private|protected|noncomputable|nonrec|unsafe|partial)\s+)*)'
    r'(?:theorem|lemma)\s+([^\s:({\[⦃]+)')
NAME_RE = re.compile(r'[^\s]+')


def module_path(module: str) -> Path:
    return BASE.joinpath(*module.split('.')).with_suffix('.lean')


def module_imports(text: str) -> list[str]:
    result = []
    for line in strip_comments(text).splitlines():
        m = IMPORT_RE.match(line)
        if m:
            result.extend(m.group(1).split())
        elif line.strip() and line.strip() not in ('module', 'prelude'):
            break
    return result


def library_modules(lib: str) -> list[str]:
    """Modules of the library reachable from its root file, in import order."""
    order: list[str] = []
    seen: set[str] = set()

    def visit(module: str) -> None:
        if module in seen:
            return
        seen.add(module)
        path = module_path(module)
        if not path.is_file():
            raise CheckFailed(f'{module} is imported but {path} does not exist')
        for dep in module_imports(path.read_text(encoding='utf-8-sig')):
            if dep == lib or dep.startswith(lib + '.'):
                visit(dep)
        order.append(module)

    visit(lib)
    return order


def unimported_files(lib: str, modules: list[str]) -> list[str]:
    folder = BASE / lib
    files = sorted(folder.rglob('*.lean')) if folder.is_dir() else []
    used = {module_path(m).resolve() for m in modules}
    return [f.relative_to(BASE).as_posix() for f in files if f.resolve() not in used]


def declarations(path: Path) -> list[str]:
    """Fully qualified names of the theorem and lemma declarations in a file."""
    scopes: list[tuple[str, str]] = []
    names: list[str] = []
    for line in strip_comments(path.read_text(encoding='utf-8-sig')).splitlines():
        words = line.split()
        if not words:
            continue
        if words[0] == 'namespace' and len(words) > 1:
            scopes.extend(('ns', part) for part in words[1].split('.'))
            continue
        if words[0] == 'section' or words[:2] == ['noncomputable', 'section']:
            scopes.append(('section', ''))
            continue
        if words[0] == 'mutual':
            scopes.append(('mutual', ''))
            continue
        if words[0] == 'end':
            count = len(words[1].split('.')) if len(words) > 1 else 1
            if count > len(scopes):
                raise CheckFailed(f'{path}: unbalanced "end"')
            del scopes[len(scopes) - count:]
            continue
        m = DECL_RE.match(line)
        if not m:
            continue
        if 'private' in m.group(1).split():
            raise CheckFailed(f'{path}: private theorem {m.group(2)} cannot be checked '
                              'from another file; make it public')
        name = m.group(2)
        if name.startswith('_root_.'):
            names.append(name[len('_root_.'):])
        else:
            names.append('.'.join([s for kind, s in scopes if kind == 'ns'] + [name]))
    return names


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


# ---------------------------------------------------------------- axiom check

ENUMERATE = '''
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let lib : Name := `{lib}
  for (n, ci) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let m := env.header.moduleNames[idx.toNat]!
    unless m == lib || lib.isPrefixOf m do continue
    -- Fields of a structure in Prop are theorems to Lean, but they are projections, not proofs.
    if env.isProjectionFn n then continue
    if let .thmInfo _ := ci then
      if !n.isInternalDetail && (← findDeclarationRanges? n).isSome then
        IO.println s!"@@THEOREM {{n}}"
'''


def write_check_file(lib: str, ws: Path, names: list[str]) -> Path:
    folder = ws / '.lake' / 'axiom-check'
    folder.mkdir(parents=True, exist_ok=True)
    path = folder / f'{lib}Axioms.lean'
    lines = [f'import {lib}', '', f'-- Temporary file written by verify_lean.py for {lib}.', '']
    lines += [f'#print axioms {name}' for name in names]
    lines.append(ENUMERATE.format(lib=lib))
    path.write_text('\n'.join(lines), encoding='utf-8')
    return path


def parse_axioms(output: str) -> dict[str, list[str]]:
    # Names may end in a prime, as in 'Kagey131.varK_eq_closed'', so match lazily up to
    # the quote that is followed by the message.
    result: dict[str, list[str]] = {}
    for name, items in re.findall(r"'([^\n]+?)' depends on axioms: \[([^\]]*)\]", output):
        result[name] = sorted(x.strip() for x in items.split(',') if x.strip())
    for name in re.findall(r"'([^\n]+?)' does not depend on any axioms", output):
        result[name] = []
    return result


# ---------------------------------------------------------------- one library

def check_library(lib: str, ws: Path, lake: str, env: dict[str, str], lean_version: str,
                  build_timeout: float, check_timeout: float, log: list[str]) -> dict:
    """Build and check one library. Log text is appended to `log` as the check runs."""
    print(f'\n=== {lib} ===', flush=True)
    print(f'   workspace {ws}', flush=True)

    modules = library_modules(lib)
    module_entries = []
    names: list[str] = []
    for module in modules:
        path = module_path(module)
        decls = declarations(path)
        names.extend(decls)
        module_entries.append({'module': module, 'file': path.relative_to(BASE).as_posix(),
                               'sha256': sha256(path), 'declarations': len(decls)})
    duplicates = sorted({n for n in names if names.count(n) > 1})
    if duplicates:
        raise CheckFailed(f'{lib}: declarations parsed twice: {duplicates}')
    stray = unimported_files(lib, modules)

    print(f'   lake build {lib}', flush=True)
    code, build_out = run_streaming([lake, 'build', lib], ws, env, build_timeout)
    log.append(f'$ lake build {lib}    (exit {code})\n{build_out}')
    if code:
        raise CheckFailed(f'lake build {lib} failed with exit code {code}')
    if "declaration uses 'sorry'" in build_out:
        raise CheckFailed(f'{lib} contains sorry')
    warnings = len(re.findall(r'^warning:', build_out, flags=re.M))

    check_file = write_check_file(lib, ws, names)
    print(f'   checking axioms of {len(names)} declarations', flush=True)
    code, check_out = run_streaming([lake, 'env', 'lean', str(check_file)], ws, env,
                                    check_timeout)
    shown = '\n'.join(line for line in check_out.splitlines()
                      if not line.startswith('@@THEOREM '))
    log.append(f'$ lake env lean {check_file.name}    (exit {code})\n{shown}\n')
    if code or re.search(r':\d+:\d+: error', check_out):
        raise CheckFailed(f'axiom check for {lib} failed with exit code {code}')

    axioms = parse_axioms(check_out)
    missing = [n for n in names if n not in axioms]
    if missing:
        raise CheckFailed(f'{lib}: no axiom report for {missing}')
    in_lean = set(re.findall(r'^@@THEOREM (\S+)\s*$', check_out, flags=re.M))
    if in_lean != set(names):
        raise CheckFailed(f'{lib}: parsed declarations differ from the theorems in the library. '
                          f'Only in Lean: {sorted(in_lean - set(names))}. '
                          f'Only parsed: {sorted(set(names) - in_lean)}')
    bad = {n: a for n, a in axioms.items() if n in set(names) and set(a) - ALLOWED}
    if bad:
        raise CheckFailed(f'{lib}: unexpected axioms {bad}')

    summary = (f'{lib}: {len(modules)} modules, {len(names)} theorem/lemma declarations, '
               f'{warnings} build warnings (linter or deprecation), '
               f'axioms within {{{", ".join(sorted(ALLOWED))}}}.')
    if stray:
        summary += f' Files not imported by {lib}.lean: {", ".join(stray)}.'
    print('   ' + summary, flush=True)
    log.insert(0, summary + '\n')
    entry = {
        'checked_at_utc': datetime.now(timezone.utc).isoformat(timespec='seconds'),
        'lean_version': lean_version,
        'mathlib_rev': mathlib_rev(ws),
        'root': f'{lib}.lean',
        'module_count': len(modules),
        'declaration_count': len(names),
        'build_warnings': warnings,
        'all_checks_passed': True,
        'modules': module_entries,
        'files_not_imported': stray,
        'axioms': {n: axioms[n] for n in names},
    }
    return entry


# ---------------------------------------------------------------- output

def tidy(text: str) -> str:
    """Replace local absolute paths so the log does not depend on the machine."""
    for folder, label in [(BASE, '.'), (Path.home(), '~')]:
        for form in {str(folder), folder.as_posix()}:
            text = text.replace(form, label)
    return text


def read_log_sections() -> dict[str, str]:
    if not LOG_FILE.is_file():
        return {}
    parts = re.split(r'^#{5} (Paper[A-Z]) #{5}\n', LOG_FILE.read_text(encoding='utf-8'),
                     flags=re.M)
    return {parts[i]: parts[i + 1] for i in range(1, len(parts) - 1, 2)}


def write_outputs(entries: dict[str, dict], logs: dict[str, str], lean_version: str) -> None:
    manifest: dict = {}
    if MANIFEST_FILE.is_file():
        try:
            manifest = json.loads(MANIFEST_FILE.read_text(encoding='utf-8'))
        except json.JSONDecodeError:
            manifest = {}
    libraries = manifest.get('libraries', {}) if isinstance(manifest.get('libraries'), dict) else {}
    libraries.update(entries)
    libraries = {lib: libraries[lib] for lib in LIBS if lib in libraries}
    manifest = {
        'written_at_utc': datetime.now(timezone.utc).isoformat(timespec='seconds'),
        'lean_version': lean_version,
        'allowed_axioms': sorted(ALLOWED),
        'all_checks_passed': all(e.get('all_checks_passed') for e in libraries.values()),
        'total_declarations': sum(e.get('declaration_count', 0) for e in libraries.values()),
        'libraries': libraries,
    }
    MANIFEST_FILE.write_text(json.dumps(manifest, indent=2, ensure_ascii=False) + '\n',
                             encoding='utf-8')

    sections = read_log_sections()
    sections.update({lib: tidy(text).rstrip() + '\n\n' for lib, text in logs.items()})
    body = ''.join(f'##### {lib} #####\n{sections[lib]}' for lib in LIBS if lib in sections)
    LOG_FILE.write_text(body, encoding='utf-8')


def main() -> int:
    if hasattr(sys.stdout, 'reconfigure'):
        sys.stdout.reconfigure(encoding='utf-8', errors='replace')
    args = parse_args()
    lake, lean, env = find_tools(args.toolchain)
    lean_version = subprocess.run([lean, '--version'], env=env, capture_output=True,
                                  text=True, check=True).stdout.strip()
    print(lean_version)
    # Check every workspace before building anything, so a wrong path leaves the outputs alone.
    workspaces: dict[str, Path] = {}
    for lib in args.libs:
        try:
            workspaces[lib] = resolve_workspace(lib, args.workspace)
        except CheckFailed as error:
            print(f'{lib}: {error}')
            return 2
    entries: dict[str, dict] = {}
    logs: dict[str, str] = {}
    failed: list[str] = []
    for lib in args.libs:
        log: list[str] = []
        try:
            entries[lib] = check_library(lib, workspaces[lib], lake, env, lean_version,
                                         args.build_timeout, args.check_timeout, log)
        except CheckFailed as error:
            failed.append(lib)
            print(f'   FAILED: {error}', flush=True)
            log.append(f'FAILED: {error}\n')
            entries[lib] = {'checked_at_utc': datetime.now(timezone.utc).isoformat(timespec='seconds'),
                            'lean_version': lean_version, 'all_checks_passed': False,
                            'error': tidy(str(error))}
        logs[lib] = '\n'.join(log)
    write_outputs(entries, logs, lean_version)
    print(f'\nWrote {LOG_FILE.name} and {MANIFEST_FILE.name}.')
    if failed:
        print(f'FAILED: {", ".join(failed)}')
        return 1
    total = sum(e['declaration_count'] for e in entries.values())
    print(f'All checks passed: {", ".join(args.libs)} ({total} declarations).')
    return 0


if __name__ == '__main__':
    sys.exit(main())
