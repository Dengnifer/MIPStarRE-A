"""Root-issued literal edit recipes for the single audit-qualified Sol job class."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import uuid

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'scripts'))
from blueprint_lean_sync import LEAN_DECL_RE, strip_lean_comments_preserve_lines
from audit_conclusion_shaped_hypotheses import _mask_lean_non_code


def git(worktree: Path, *args: str) -> str:
    env = {key: value for key, value in os.environ.items() if not key.startswith('GIT_')}
    return subprocess.check_output(['git', '--no-replace-objects', '-C', str(worktree), *args],
                                   text=True, env=env, stderr=subprocess.PIPE)


def digest(value: dict) -> str:
    return hashlib.sha256(json.dumps(value, sort_keys=True).encode()).hexdigest()


def recipe_outputs(recipe: dict) -> dict[str, str]:
    """Compute the exact approved artifact; no global replacement or new file is permitted."""
    worktree = Path(recipe['worktree']).resolve(strict=True)
    base = recipe['base_sha']
    edits, renames = recipe['allowed_edits'], recipe.get('renames', {})
    if (not re.fullmatch('[0-9a-f]{40}', base) or not recipe.get('review_reference') or
            not isinstance(edits, list) or not 1 <= len(edits) <= 2 or
            not isinstance(renames, dict)):
        raise ValueError('invalid bounded edit recipe')
    outputs, originals, changed = {}, {}, 0
    for edit in edits:
        path = edit['path']
        if (path in outputs or not path.startswith('MIPStarRE/') or
                not path.endswith('.lean') or '..' in Path(path).parts):
            raise ValueError('recipe must name at most two existing Lean files')
        entry = git(worktree, 'ls-tree', base, '--', path).split()
        if len(entry) != 4 or entry[:2] != ['100644', 'blob'] or entry[2] != edit['before_blob']:
            raise ValueError('recipe base blob or regular-file mode differs')
        original = git(worktree, 'show', f'{base}:{path}')
        lines = original.splitlines(keepends=True)
        last_end = 0
        for hunk in edit['hunks']:
            start = hunk['old_start'] - 1
            before, after = hunk['before'], hunk['after']
            if (not before or len(before) != len(after) or start < last_end or
                    any(not isinstance(line, str) or '\n' in line for line in before + after) or
                    lines[start:start + len(before)] != [line + '\n' for line in before]):
                raise ValueError('recipe occurrence or literal before/after differs')
            lines[start:start + len(before)] = [line + '\n' for line in after]
            last_end = start + len(before)
            changed += sum(old != new for old, new in zip(before, after)) * 2
        originals[path], outputs[path] = original, ''.join(lines)
    if not 0 < changed <= 12:
        raise ValueError('recipe exceeds twelve added plus removed lines')
    declarations = {match[2] for text in originals.values()
                    for match in LEAN_DECL_RE.finditer(_mask_lean_non_code(text))
                    if match[1] in ('theorem', 'lemma')}
    if (any(not re.fullmatch('[A-Za-z_][A-Za-z0-9_]*', name)
            for pair in renames.items() for name in pair) or
            not renames.keys() <= declarations or len(set(renames.values())) != len(renames)):
        raise ValueError('only exact existing theorem/lemma identifiers may be renamed')
    inverse = {new: old for old, new in renames.items()}
    for path, after in outputs.items():
        restored = after
        tokens = list(re.finditer(r"[\w']+", _mask_lean_non_code(after)))
        for token in reversed(tokens):
            if token[0] in inverse:
                restored = restored[:token.start()] + inverse[token[0]] + restored[token.end():]
        if (strip_lean_comments_preserve_lines(originals[path]) !=
                strip_lean_comments_preserve_lines(restored)):
            raise ValueError('recipe changes statement/proof/string content beyond approved names')
        for command in ('import', 'attribute', '@['):
            if ([line for line in originals[path].splitlines() if line.lstrip().startswith(command)] !=
                    [line for line in after.splitlines() if line.lstrip().startswith(command)]):
                raise ValueError('imports and attributes are outside the qualified scope')
    return outputs


def read_job(reference: str) -> tuple[dict, Path]:
    from native_review import verify_root
    cache = Path(os.environ.get('MIPSTARRE_CACHE_ROOT', Path.home() / '.cache/mipstarre-dev'))
    path = Path(reference)
    if path.is_symlink() or path.resolve().parent != (cache / 'model-jobs').resolve():
        raise ValueError('a canonical root-issued model job is required')
    request = json.loads(path.read_text())
    if path.stem != request['nonce'] or request['digest'] != digest({
            key: value for key, value in request.items() if key != 'digest'}):
        raise ValueError('model job identity or digest changed')
    root = verify_root(cache, request['root_thread_id'])
    if any(root[key] != request[key] for key in ('pid', 'start')):
        raise ValueError('model job root changed')
    recipe_outputs(request['recipe'])
    return request, Path(request['recipe']['worktree']).resolve()


def validate_job(reference: str, worktree: str | None = None, *, admission: bool = False,
                 completed: bool = False) -> dict:
    request, target = read_job(reference)
    if worktree and target != Path(worktree).resolve():
        raise ValueError('model job worktree differs')
    if admission and (os.environ.get('CODEX_THREAD_ID') != request['root_thread_id'] or
            git(target, 'rev-parse', 'HEAD').strip() != request['recipe']['base_sha'] or
            git(target, 'status', '--porcelain', '--untracked-files=all').strip()):
        raise ValueError('Sol requires its issuing root and clean exact job base')
    if completed:
        outputs = recipe_outputs(request['recipe'])
        changed = set(git(target, 'diff', '--name-only', request['recipe']['base_sha']).splitlines())
        if changed != set(outputs) or git(target, 'ls-files', '--others', '--exclude-standard').strip():
            raise ValueError('Sol artifact contains unlisted paths or an incomplete recipe')
        for name, expected in outputs.items():
            path = target / name
            index = git(target, 'ls-files', '--stage', '--', name).split()
            if (path.is_symlink() or index[:1] != ['100644'] or index[2:3] != ['0'] or
                    path.stat().st_mode & 0o111 or path.read_text() != expected or
                    git(target, 'show', ':' + name) not in
                    (git(target, 'show', request['recipe']['base_sha'] + ':' + name), expected)):
                raise ValueError('Sol artifact differs from the exact authorized recipe')
    return request


def main() -> None:
    from native_review import verify_root
    from telemetry import now_ts
    from wf_util import atomic_write
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('recipe', type=Path)
    parser.add_argument('--root-thread-id', required=True)
    args = parser.parse_args()
    if os.environ.get('CODEX_THREAD_ID') != args.root_thread_id:
        parser.exit(4, 'only the native Astra root may issue a model job\n')
    cache = Path(os.environ.get('MIPSTARRE_CACHE_ROOT', Path.home() / '.cache/mipstarre-dev'))
    root = verify_root(cache, args.root_thread_id)
    recipe = json.loads(args.recipe.read_text())
    recipe_outputs(recipe)
    request = dict(nonce=uuid.uuid4().hex, root_thread_id=args.root_thread_id,
                   created=now_ts(), pid=root['pid'], start=root['start'], recipe=recipe)
    request['digest'] = digest(request)
    path = cache / 'model-jobs' / (request['nonce'] + '.json')
    path.parent.mkdir(parents=True, exist_ok=True)
    atomic_write(path, json.dumps(request) + '\n')
    print(path)
    print('Native model binding: ' + request['digest'])


if __name__ == '__main__':
    main()
