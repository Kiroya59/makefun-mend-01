// mend — one patch tool for every AI edit format.
//
// Applies a patch (unified diff, SEARCH/REPLACE blocks, V4A, or JSON edits)
// to the tree of text files rooted at the working directory, all or nothing.
// Written from SPEC.md. Node 22, standard library only.
//
// Usage: node main.ts [--format=NAME] [--check] [--strict] [PATCH]

import { mkdirSync, readFileSync, rmSync, statSync, writeFileSync, writeSync } from 'node:fs';
import { dirname } from 'node:path';

const FORMAT_NAMES = ['auto', 'unified', 'search-replace', 'v4a', 'json'];

/** A parse failure: exit 2 with `error: parse <line>`. */
class ParseError {
  readonly line: number;
  constructor(line: number) {
    this.line = line;
  }
}

/** One edit's failure: exit 1 with `error: <code> <path>`. */
class EditError {
  readonly code: string;
  readonly path: string;
  constructor(code: string, path: string) {
    this.code = code;
    this.path = path;
  }
}

type EditFn = (tree: FileTree) => void;

/** A line of replacement text: either copied from the file's own matched
 *  line (context, `fromOld` is its index in the old lines) or fresh text. */
interface FreshLine {
  text: string;
  fromOld: number | null;
}

/** Split patch text into lines: split at \n, drop one trailing \r per line,
 *  drop the empty piece after a final \n. */
function splitPatchText(text: string): string[] {
  if (text === '') return [];
  const parts = text.split('\n');
  if (text.endsWith('\n')) parts.pop();
  return parts.map((l) => (l.endsWith('\r') ? l.slice(0, -1) : l));
}

function isBlankLine(s: string): boolean {
  return s.trim() === '';
}

function isSafePath(p: string): boolean {
  if (p === '' || p.startsWith('/') || p.includes('\\')) return false;
  return p.split('/').every((seg) => seg !== '' && seg !== '.' && seg !== '..');
}

/** A file as lines plus its line break and whether it ends with one. */
interface Doc {
  br: string;
  lines: string[];
  finalBreak: boolean;
}

function readDoc(text: string): Doc {
  if (text === '') return { br: '\n', lines: [], finalBreak: false };
  const lf = text.indexOf('\n');
  const br = lf > 0 && text[lf - 1] === '\r' ? '\r\n' : '\n';
  const finalBreak = text.endsWith(br);
  const lines = text.split(br);
  if (finalBreak) lines.pop();
  return { br, lines, finalBreak };
}

function writeDoc(d: Doc): string {
  if (d.lines.length === 0) return '';
  return d.lines.join(d.br) + (d.finalBreak ? d.br : '');
}

function fileIsCrlf(text: string): boolean {
  const lf = text.indexOf('\n');
  return lf > 0 && text[lf - 1] === '\r';
}

/** True when `p` is a directory on disk. A directory is not a file, so the
 *  tree reads it as absent, but a create or a move to that path still fails
 *  with `exists`: the path exists (SPEC section 2). */
function isDirOnDisk(p: string): boolean {
  try {
    return statSync(p).isDirectory();
  } catch {
    return false;
  }
}

/** True when an edit may not create a file at `p`: a file is there in the
 *  tree as earlier edits left it, or a directory is there on disk. */
function createBlocked(tree: FileTree, p: string): boolean {
  return tree.current(p) !== null || isDirOnDisk(p);
}

/** The tree as edits leave it: `now` holds changed paths (null = deleted),
 *  everything else is read from disk on demand and cached as original. */
class FileTree {
  private originals = new Map<string, string | null>();
  readonly now = new Map<string, string | null>();
  readonly moves: Array<[string, string]> = [];

  original(p: string): string | null {
    if (!this.originals.has(p)) {
      let v: string | null = null;
      try {
        if (statSync(p).isFile()) v = readFileSync(p, 'utf8');
      } catch {
        v = null;
      }
      this.originals.set(p, v);
    }
    return this.originals.get(p)!;
  }

  current(p: string): string | null {
    return this.now.has(p) ? this.now.get(p)! : this.original(p);
  }

  set(p: string, text: string | null): void {
    this.now.set(p, text);
  }

  snapshot(): Map<string, string | null> {
    return new Map(this.now);
  }

  restore(snap: Map<string, string | null>, movesLen: number): void {
    this.now.clear();
    for (const [k, v] of snap) this.now.set(k, v);
    this.moves.length = movesLen;
  }
}

// ---------------------------------------------------------------- matching

function trimForTier(s: string, tier: number): string {
  if (tier === 0) return s;
  const noTrail = s.replace(/[ \t]+$/, '');
  if (tier === 1) return noTrail;
  return noTrail.replace(/^[ \t]+/, '');
}

function leadingWs(s: string): string {
  const m = /^[ \t]*/.exec(s);
  return m ? m[0] : '';
}

/** First tier (0, then 1, then 2) at which `old` occurs in `lines`, with every
 *  occurrence position at that tier; null when it occurs at no tier. */
function locate(lines: string[], old: string[], strict: boolean): { tier: number; at: number[] } | null {
  const top = strict ? 0 : 2;
  for (let tier = 0; tier <= top; tier++) {
    const want = old.map((l) => trimForTier(l, tier));
    const at: number[] = [];
    for (let i = 0; i + old.length <= lines.length; i++) {
      let ok = true;
      for (let j = 0; j < old.length; j++) {
        if (trimForTier(lines[i + j], tier) !== want[j]) {
          ok = false;
          break;
        }
      }
      if (ok) at.push(i);
    }
    if (at.length > 0) return { tier, at };
  }
  return null;
}

/** Replace `oldLen` lines at `pos` with `fresh`. Context lines come from the
 *  file's own matched lines; at tier 2 every other line is re-indented from
 *  the old lines' first indent to the file's first matched indent. */
function spliceFresh(lines: string[], pos: number, oldLen: number, fresh: FreshLine[], tier: number, old: string[]): string[] {
  const out = lines.slice(0, pos);
  const fileLead = tier === 2 && old.length > 0 ? leadingWs(lines[pos]) : '';
  const oldLead = tier === 2 && old.length > 0 ? leadingWs(old[0]) : '';
  for (const item of fresh) {
    if (item.fromOld !== null) {
      out.push(lines[pos + item.fromOld]);
      continue;
    }
    let t = item.text;
    if (tier === 2 && t !== '' && t.trim() !== '' && t.startsWith(oldLead)) {
      t = fileLead + t.slice(oldLead.length);
    }
    out.push(t);
  }
  out.push(...lines.slice(pos + oldLen));
  return out;
}

// ------------------------------------------------------------ format detect

function detectFormat(lines: string[]): string | null {
  const first = lines.findIndex((l) => !isBlankLine(l));
  if (first < 0) return null;
  if (lines[first].trim() === '*** Begin Patch') return 'v4a';
  const c = lines[first].trimStart()[0];
  if (c === '[' || c === '{') return 'json';
  if (lines.some((l) => l.trimEnd() === '<<<<<<< SEARCH')) return 'search-replace';
  if (
    lines.some(
      (l, i) => l.startsWith('diff --git ') || (l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')),
    )
  ) {
    return 'unified';
  }
  return null;
}

// ------------------------------------------------------------ unified diffs

interface Hunk {
  start: number;
  body: string[];
}

interface Section {
  oldPath: string | null;
  newPath: string | null;
  create: boolean;
  remove: boolean;
  hunks: Hunk[];
}

/** A `---`/`+++` path: text after the marker, up to the first tab, trimmed;
 *  `/dev/null` is no file; a leading `a/` or `b/` is dropped. */
function headerPath(raw: string): string | null {
  let t = raw.split('\t')[0].trim();
  if (t === '/dev/null') return null;
  if (t.startsWith('a/') || t.startsWith('b/')) t = t.slice(2);
  return t;
}

function parseUnified(lines: string[], strict: boolean): EditFn[] {
  const sections: Section[] = [];
  const n = lines.length;
  const pairAt = (i: number): boolean => lines[i].startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ');
  let i = 0;
  while (i < n) {
    const line = lines[i];
    let sec: Section | null = null;
    if (line.startsWith('diff --git ')) {
      const m = /^diff --git a\/(\S+) b\/(\S+)$/.exec(line);
      if (!m) throw new ParseError(i + 1);
      sec = { oldPath: m[1], newPath: m[2], create: false, remove: false, hunks: [] };
      i += 1;
    } else if (pairAt(i)) {
      sec = { oldPath: null, newPath: null, create: false, remove: false, hunks: [] };
    } else {
      if (line.startsWith('@@')) throw new ParseError(i + 1);
      i += 1;
      continue;
    }
    sections.push(sec);
    let pairSeen = false;
    let renameFrom: string | null = null;
    let renameTo: string | null = null;
    // Header lines, up to the first hunk or the next section.
    while (i < n) {
      const h = lines[i];
      if (h.startsWith('--- ')) {
        if ((lines[i + 1] ?? '').startsWith('+++ ')) {
          sec.oldPath = headerPath(h.slice(4));
          sec.newPath = headerPath(lines[i + 1].slice(4));
          pairSeen = true;
          i += 2;
        } else {
          throw new ParseError(i + 2);
        }
      } else if (h.startsWith('+++ ')) {
        sec.newPath = headerPath(h.slice(4));
        i += 1;
      } else if (h.startsWith('rename from ')) {
        renameFrom = h.slice('rename from '.length);
        i += 1;
      } else if (h.startsWith('rename to ')) {
        renameTo = h.slice('rename to '.length);
        i += 1;
      } else if (h.startsWith('new file mode')) {
        sec.create = true;
        i += 1;
      } else if (h.startsWith('deleted file mode')) {
        sec.remove = true;
        i += 1;
      } else if (h.startsWith('@@') || h.startsWith('diff --git ') || pairAt(i)) {
        break;
      } else {
        i += 1; // index, mode, similarity and any other line: ignored
      }
    }
    // Hunks of this section.
    while (i < n && lines[i].startsWith('@@')) {
      const m = /^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@/.exec(lines[i]);
      if (!m) throw new ParseError(i + 1);
      const start = parseInt(m[1], 10);
      i += 1;
      const body: string[] = [];
      while (i < n) {
        const b = lines[i];
        if (b.startsWith('diff --git ')) break;
        if (b.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) break;
        if (b === '' || b.startsWith(' ') || b.startsWith('-') || b.startsWith('+') || b.startsWith('\\')) {
          body.push(b);
          i += 1;
        } else {
          break;
        }
      }
      while (body.length > 0 && body[body.length - 1] === '') body.pop();
      sec.hunks.push({ start, body });
    }
    if (!pairSeen) {
      if (renameFrom !== null) sec.oldPath = renameFrom;
      if (renameTo !== null) sec.newPath = renameTo;
    }
  }
  return sections.map((sec) => unifiedEdit(sec, strict));
}

/** Split a hunk body into old lines, new lines (with context marked), and
 *  whether a `\` line follows the hunk's last context or `+` line. */
function hunkParts(body: string[]): { oldLines: string[]; fresh: FreshLine[]; noEol: boolean } {
  const oldLines: string[] = [];
  const fresh: FreshLine[] = [];
  let lastCtxPlus = -1;
  for (let k = 0; k < body.length; k++) {
    if (body[k].startsWith(' ') || body[k].startsWith('+')) lastCtxPlus = k;
  }
  const noEol =
    lastCtxPlus >= 0 && lastCtxPlus + 1 < body.length && body[lastCtxPlus + 1].startsWith('\\');
  for (const b of body) {
    if (b === '' || b.startsWith(' ')) {
      const text = b === '' ? '' : b.slice(1);
      oldLines.push(text);
      fresh.push({ text, fromOld: oldLines.length - 1 });
    } else if (b.startsWith('-')) {
      oldLines.push(b.slice(1));
    } else if (b.startsWith('+')) {
      fresh.push({ text: b.slice(1), fromOld: null });
    }
    // `\` lines are markers only.
  }
  return { oldLines, fresh, noEol };
}

function unifiedEdit(sec: Section, strict: boolean): EditFn {
  return (tree) => {
    const oldP = sec.oldPath;
    const newP = sec.newPath;
    if ((sec.create || oldP === null) && newP !== null) {
      if (!isSafePath(newP)) throw new EditError('unsafe', newP);
      if (createBlocked(tree, newP)) throw new EditError('exists', newP);
      const plus: string[] = [];
      let lastPlus: { h: number; k: number } | null = null;
      sec.hunks.forEach((h, hi) => {
        h.body.forEach((b, k) => {
          if (b.startsWith('+')) {
            plus.push(b.slice(1));
            lastPlus = { h: hi, k };
          }
        });
      });
      let noEol = false;
      if (lastPlus !== null) {
        const body = sec.hunks[lastPlus.h].body;
        if (lastPlus.k + 1 < body.length && body[lastPlus.k + 1].startsWith('\\')) noEol = true;
      }
      tree.set(newP, plus.length === 0 ? '' : plus.join('\n') + (noEol ? '' : '\n'));
      return;
    }
    if ((sec.remove || newP === null) && oldP !== null) {
      if (!isSafePath(oldP)) throw new EditError('unsafe', oldP);
      if (tree.current(oldP) === null) throw new EditError('missing', oldP);
      tree.set(oldP, null);
      return;
    }
    if (oldP === null || newP === null) return; // both /dev/null: nothing to do
    if (!isSafePath(oldP)) throw new EditError('unsafe', oldP);
    if (!isSafePath(newP)) throw new EditError('unsafe', newP);
    const before = tree.current(oldP);
    if (before === null) throw new EditError('missing', oldP);
    if (oldP !== newP && createBlocked(tree, newP)) throw new EditError('exists', newP);
    const doc = readDoc(before);
    let drift = 0;
    for (const h of sec.hunks) {
      const { oldLines, fresh, noEol } = hunkParts(h.body);
      if (oldLines.length > 0) {
        const found = locate(doc.lines, oldLines, strict);
        if (!found) throw new EditError('no-match', oldP);
        const target = h.start - 1 + drift;
        let best = found.at[0];
        let bestDist = Math.abs(best - target);
        for (const p of found.at) {
          const dist = Math.abs(p - target);
          if (dist < bestDist) {
            best = p;
            bestDist = dist;
          }
        }
        const touchesEnd = best + oldLines.length === doc.lines.length;
        doc.lines = spliceFresh(doc.lines, best, oldLines.length, fresh, found.tier, oldLines);
        if (touchesEnd) doc.finalBreak = !noEol;
        drift += fresh.length - oldLines.length;
      } else {
        const at = Math.min(h.start + drift, doc.lines.length);
        const touchesEnd = at === doc.lines.length;
        doc.lines = spliceFresh(doc.lines, at, 0, fresh, 0, []);
        if (touchesEnd) doc.finalBreak = !noEol;
        drift += fresh.length;
      }
    }
    const out = writeDoc(doc);
    if (oldP !== newP) {
      tree.set(newP, out);
      tree.set(oldP, null);
      tree.moves.push([oldP, newP]);
    } else {
      tree.set(oldP, out);
    }
  };
}

// ------------------------------------------------------- SEARCH/REPLACE

function parseSearchReplace(lines: string[], strict: boolean): EditFn[] {
  const edits: EditFn[] = [];
  const n = lines.length;
  let prevEnd = 0;
  let prevPath: string | null = null;
  let i = 0;
  while (i < n) {
    if (lines[i].trimEnd() !== '<<<<<<< SEARCH') {
      i += 1;
      continue;
    }
    const searchLine = i;
    let path: string | null = null;
    for (let k = searchLine - 1; k >= prevEnd; k--) {
      const t = lines[k].trim();
      if (t === '' || t.startsWith('```')) continue;
      path = t;
      break;
    }
    if (path === null) path = prevPath;
    if (path === null) throw new ParseError(searchLine + 1);
    let sep = -1;
    let j = searchLine + 1;
    while (j < n) {
      const t = lines[j].trimEnd();
      if (t === '=======') {
        sep = j;
        break;
      }
      if (t === '>>>>>>> REPLACE' || t === '<<<<<<< SEARCH') break;
      j += 1;
    }
    if (sep < 0) throw new ParseError(searchLine + 1);
    let end = -1;
    let k = sep + 1;
    while (k < n) {
      const t = lines[k].trimEnd();
      if (t === '>>>>>>> REPLACE') {
        end = k;
        break;
      }
      if (t === '<<<<<<< SEARCH') break;
      k += 1;
    }
    if (end < 0) throw new ParseError(searchLine + 1);
    const oldLines = lines.slice(searchLine + 1, sep);
    const newLines = lines.slice(sep + 1, end);
    edits.push(srEdit(path, oldLines, newLines, strict));
    prevPath = path;
    prevEnd = end + 1;
    i = end + 1;
  }
  return edits;
}

function srEdit(path: string, oldLines: string[], newLines: string[], strict: boolean): EditFn {
  return (tree) => {
    if (!isSafePath(path)) throw new EditError('unsafe', path);
    if (oldLines.length === 0) {
      if (createBlocked(tree, path)) throw new EditError('exists', path);
      tree.set(path, newLines.length === 0 ? '' : newLines.join('\n') + '\n');
      return;
    }
    const cur = tree.current(path);
    if (cur === null) throw new EditError('missing', path);
    const doc = readDoc(cur);
    const found = locate(doc.lines, oldLines, strict);
    if (!found) throw new EditError('no-match', path);
    if (found.at.length > 1) throw new EditError('ambiguous', path);
    const fresh: FreshLine[] = newLines.map((t) => ({ text: t, fromOld: null }));
    doc.lines = spliceFresh(doc.lines, found.at[0], oldLines.length, fresh, found.tier, oldLines);
    tree.set(path, writeDoc(doc));
  };
}

// ------------------------------------------------------------------- V4A

interface V4aChunk {
  anchor: string | null;
  eof: boolean;
  oldLines: string[];
  fresh: FreshLine[];
}

function parseV4a(lines: string[], strict: boolean): EditFn[] {
  const n = lines.length;
  const first = lines.findIndex((l) => !isBlankLine(l));
  if (first < 0) throw new ParseError(1);
  if (lines[first].trim() !== '*** Begin Patch') throw new ParseError(first + 1);
  let last = -1;
  for (let k = n - 1; k >= 0; k--) {
    if (!isBlankLine(lines[k])) {
      last = k;
      break;
    }
  }
  if (lines[last].trim() !== '*** End Patch') throw new ParseError(n + 1);
  const edits: EditFn[] = [];
  let i = first + 1;
  while (i < last) {
    const line = lines[i];
    if (isBlankLine(line)) {
      i += 1;
      continue;
    }
    let kind: string | null = null;
    let path = '';
    if (line.startsWith('*** Add File: ')) {
      kind = 'add';
      path = line.slice('*** Add File: '.length).trim();
    } else if (line.startsWith('*** Delete File: ')) {
      kind = 'delete';
      path = line.slice('*** Delete File: '.length).trim();
    } else if (line.startsWith('*** Update File: ')) {
      kind = 'update';
      path = line.slice('*** Update File: '.length).trim();
    } else {
      throw new ParseError(i + 1);
    }
    const headLine = i;
    i += 1;
    const raw: string[] = [];
    while (i < last) {
      const l = lines[i];
      if (l.startsWith('*** Add File: ') || l.startsWith('*** Delete File: ') || l.startsWith('*** Update File: ')) break;
      raw.push(l);
      i += 1;
    }
    while (raw.length > 0 && isBlankLine(raw[raw.length - 1])) raw.pop();
    const lineNo = (k: number): number => headLine + 2 + k;
    if (kind === 'add') {
      const fileLines: string[] = [];
      for (let k = 0; k < raw.length; k++) {
        const l = raw[k];
        if (l === '') fileLines.push('');
        else if (l.startsWith('+')) fileLines.push(l.slice(1));
        else throw new ParseError(lineNo(k));
      }
      edits.push((tree) => {
        if (!isSafePath(path)) throw new EditError('unsafe', path);
        if (createBlocked(tree, path)) throw new EditError('exists', path);
        tree.set(path, fileLines.length === 0 ? '' : fileLines.join('\n') + '\n');
      });
    } else if (kind === 'delete') {
      for (let k = 0; k < raw.length; k++) {
        if (!isBlankLine(raw[k])) throw new ParseError(lineNo(k));
      }
      edits.push((tree) => {
        if (!isSafePath(path)) throw new EditError('unsafe', path);
        if (tree.current(path) === null) throw new EditError('missing', path);
        tree.set(path, null);
      });
    } else {
      edits.push(v4aUpdateEdit(path, raw, headLine, strict));
    }
  }
  return edits;
}

function v4aUpdateEdit(path: string, raw: string[], headLine: number, strict: boolean): EditFn {
  const lineNo = (k: number): number => headLine + 2 + k;
  let moveTo: string | null = null;
  let idx = 0;
  if (raw.length > 0 && raw[0].startsWith('*** Move to: ')) {
    moveTo = raw[0].slice('*** Move to: '.length).trim();
    idx = 1;
  }
  const chunks: V4aChunk[] = [];
  let cur: V4aChunk | null = null;
  let started = false;
  const close = (): void => {
    if (cur !== null) {
      chunks.push(cur);
      cur = null;
    }
  };
  for (; idx < raw.length; idx++) {
    const l = raw[idx];
    if (l.startsWith('@@')) {
      close();
      cur = { anchor: l.slice(2).trim(), eof: false, oldLines: [], fresh: [] };
      started = true;
    } else if (l === '*** End of File') {
      if (cur === null) throw new ParseError(lineNo(idx));
      cur.eof = true;
      close();
    } else if (l.startsWith('*** ')) {
      throw new ParseError(lineNo(idx));
    } else if (l.startsWith(' ') || l.startsWith('-') || l.startsWith('+') || l === '') {
      if (l === '' && cur === null && chunks.length > 0) continue; // blank between chunks
      if (cur === null) {
        if (chunks.length === 0 && !started) {
          cur = { anchor: null, eof: false, oldLines: [], fresh: [] };
          started = true;
        } else {
          throw new ParseError(lineNo(idx));
        }
      }
      if (l === '' || l.startsWith(' ')) {
        const text = l === '' ? '' : l.slice(1);
        cur.oldLines.push(text);
        cur.fresh.push({ text, fromOld: cur.oldLines.length - 1 });
      } else if (l.startsWith('-')) {
        cur.oldLines.push(l.slice(1));
      } else {
        cur.fresh.push({ text: l.slice(1), fromOld: null });
      }
    } else {
      throw new ParseError(lineNo(idx));
    }
  }
  close();
  if (chunks.length === 0 && moveTo === null) throw new ParseError(headLine + 1);
  return (tree) => {
    if (!isSafePath(path)) throw new EditError('unsafe', path);
    if (moveTo !== null && !isSafePath(moveTo)) throw new EditError('unsafe', moveTo);
    const curText = tree.current(path);
    if (curText === null) throw new EditError('missing', path);
    if (moveTo !== null && createBlocked(tree, moveTo)) throw new EditError('exists', moveTo);
    const doc = readDoc(curText);
    let cursor = 0;
    for (const ch of chunks) {
      if (ch.anchor !== null && ch.anchor !== '') {
        let foundAt: number | null = null;
        const top = strict ? 0 : 2;
        for (let tier = 0; tier <= top && foundAt === null; tier++) {
          for (let k = cursor; k < doc.lines.length; k++) {
            if (trimForTier(doc.lines[k], tier) === trimForTier(ch.anchor, tier)) {
              foundAt = k;
              break;
            }
          }
        }
        if (foundAt === null) throw new EditError('no-match', path);
        cursor = foundAt + 1;
      }
      if (ch.oldLines.length === 0) {
        const at = ch.eof ? doc.lines.length : cursor;
        doc.lines = spliceFresh(doc.lines, at, 0, ch.fresh, 0, []);
        cursor = at + ch.fresh.length;
      } else {
        let hit: { tier: number; pos: number } | null = null;
        const top = strict ? 0 : 2;
        for (let tier = 0; tier <= top && hit === null; tier++) {
          const want = ch.oldLines.map((l) => trimForTier(l, tier));
          for (let p = cursor; p + ch.oldLines.length <= doc.lines.length; p++) {
            let ok = true;
            for (let j = 0; j < ch.oldLines.length; j++) {
              if (trimForTier(doc.lines[p + j], tier) !== want[j]) {
                ok = false;
                break;
              }
            }
            if (ok) {
              if (ch.eof && p + ch.oldLines.length !== doc.lines.length) continue;
              hit = { tier, pos: p };
              break;
            }
          }
        }
        if (hit === null) throw new EditError('no-match', path);
        doc.lines = spliceFresh(doc.lines, hit.pos, ch.oldLines.length, ch.fresh, hit.tier, ch.oldLines);
        cursor = hit.pos + ch.fresh.length;
      }
    }
    const out = writeDoc(doc);
    if (moveTo !== null) {
      tree.set(moveTo, out);
      tree.set(path, null);
      tree.moves.push([path, moveTo]);
    } else {
      tree.set(path, out);
    }
  };
}

// ------------------------------------------------------------------ JSON

/** One JSON edit object, or null when the value is not one. */
function jsonEdit(v: unknown): EditFn | null {
  if (v === null || typeof v !== 'object' || Array.isArray(v)) return null;
  const o = v as Record<string, unknown>;
  if (typeof o.path !== 'string') return null;
  const p = o.path;
  if (o.command === 'create') {
    if (typeof o.file_text !== 'string') return null;
    const text = o.file_text;
    return (tree) => {
      if (!isSafePath(p)) throw new EditError('unsafe', p);
      if (createBlocked(tree, p)) throw new EditError('exists', p);
      tree.set(p, text);
    };
  }
  if (o.command === 'str_replace') {
    if (typeof o.old_str !== 'string' || o.old_str === '') return null;
    if (o.new_str !== undefined && typeof o.new_str !== 'string') return null;
    const oldStr = o.old_str;
    const newStr = (o.new_str as string | undefined) ?? '';
    return (tree) => {
      if (!isSafePath(p)) throw new EditError('unsafe', p);
      const cur = tree.current(p);
      if (cur === null) throw new EditError('missing', p);
      const crlf = fileIsCrlf(cur);
      const norm = (s: string): string => (crlf ? s.replaceAll('\r\n', '\n') : s);
      const body = norm(cur);
      const old = norm(oldStr);
      const rep = norm(newStr);
      let count = 0;
      let at = -1;
      for (let k = body.indexOf(old); k >= 0; k = body.indexOf(old, k + 1)) {
        count += 1;
        if (at < 0) at = k;
      }
      if (count === 0) throw new EditError('no-match', p);
      if (count > 1) throw new EditError('ambiguous', p);
      const out = body.slice(0, at) + rep + body.slice(at + old.length);
      tree.set(p, crlf ? out.replaceAll('\n', '\r\n') : out);
    };
  }
  if (o.command === 'insert') {
    if (typeof o.insert_line !== 'number' || !Number.isInteger(o.insert_line)) return null;
    if (typeof o.new_str !== 'string') return null;
    const atLine = o.insert_line;
    const add = splitPatchText(o.new_str);
    return (tree) => {
      if (!isSafePath(p)) throw new EditError('unsafe', p);
      const cur = tree.current(p);
      if (cur === null) throw new EditError('missing', p);
      const doc = readDoc(cur);
      if (atLine < 0 || atLine > doc.lines.length) throw new EditError('no-match', p);
      doc.lines.splice(atLine, 0, ...add);
      tree.set(p, writeDoc(doc));
    };
  }
  return null;
}

function parseJson(text: string, lines: string[]): EditFn[] {
  const first = lines.findIndex((l) => !isBlankLine(l));
  if (first < 0) throw new ParseError(1);
  const edits: EditFn[] = [];
  if (lines[first].trimStart().startsWith('[')) {
    let v: unknown;
    try {
      v = JSON.parse(text);
    } catch {
      throw new ParseError(first + 1);
    }
    if (!Array.isArray(v)) throw new ParseError(first + 1);
    for (const item of v) {
      const e = jsonEdit(item);
      if (e === null) throw new ParseError(first + 1);
      edits.push(e);
    }
    return edits;
  }
  lines.forEach((l, idx) => {
    if (isBlankLine(l)) return;
    let e: EditFn | null = null;
    try {
      e = jsonEdit(JSON.parse(l));
    } catch {
      e = null;
    }
    if (e === null) throw new ParseError(idx + 1);
    edits.push(e);
  });
  return edits;
}

// ------------------------------------------------------------------- main

function usageResult(): { code: number; out: string[] } {
  return { code: 2, out: ['error: usage'] };
}

function runCli(args: string[]): { code: number; out: string[] } {
  let format: string | null = null;
  let check = false;
  let strict = false;
  const pos: string[] = [];
  let ended = false;
  for (const a of args) {
    if (!ended && a === '--') {
      ended = true;
    } else if (!ended && a.startsWith('-') && a !== '-') {
      if (a.startsWith('--format=')) {
        const v = a.slice('--format='.length);
        if (format !== null || !FORMAT_NAMES.includes(v)) return usageResult();
        format = v;
      } else if (a === '--check') {
        if (check) return usageResult();
        check = true;
      } else if (a === '--strict') {
        if (strict) return usageResult();
        strict = true;
      } else {
        return usageResult();
      }
    } else {
      pos.push(a);
    }
  }
  if (pos.length > 1) return usageResult();
  const patchArg = pos.length === 0 ? null : pos[0];
  let text = '';
  if (patchArg === null || patchArg === '-') {
    try {
      text = readFileSync(0, 'utf8');
    } catch {
      text = '';
    }
  } else {
    try {
      text = readFileSync(patchArg, 'utf8');
    } catch {
      return { code: 2, out: ['error: no-patch'] };
    }
  }
  const lines = splitPatchText(text);
  const kind = format === null || format === 'auto' ? detectFormat(lines) : format;
  if (kind === null) return { code: 2, out: ['error: format'] };
  let edits: EditFn[];
  try {
    edits =
      kind === 'unified'
        ? parseUnified(lines, strict)
        : kind === 'search-replace'
          ? parseSearchReplace(lines, strict)
          : kind === 'v4a'
            ? parseV4a(lines, strict)
            : parseJson(text, lines);
    if (edits.length === 0) throw new ParseError(1);
  } catch (e) {
    if (e instanceof ParseError) return { code: 2, out: [`error: parse ${e.line}`] };
    throw e;
  }
  const tree = new FileTree();
  const fails: EditError[] = [];
  for (const edit of edits) {
    const snap = tree.snapshot();
    const movesLen = tree.moves.length;
    try {
      edit(tree);
    } catch (e) {
      if (!(e instanceof EditError)) throw e;
      tree.restore(snap, movesLen);
      fails.push(e);
    }
  }
  if (fails.length > 0) {
    return {
      code: 1,
      out: [...fails.map((f) => `error: ${f.code} ${f.path}`), `failed: ${fails.length} of ${edits.length} edits`],
    };
  }
  const rows: { key: string; line: string }[] = [];
  const movedOld = new Set<string>();
  const movedNew = new Set<string>();
  for (const [o, nw] of tree.moves) {
    if (
      tree.original(o) !== null &&
      tree.current(o) === null &&
      tree.original(nw) === null &&
      tree.current(nw) !== null
    ) {
      rows.push({ key: nw, line: `R ${o} -> ${nw}` });
      movedOld.add(o);
      movedNew.add(nw);
    }
  }
  for (const p of [...tree.now.keys()]) {
    if (movedOld.has(p) || movedNew.has(p)) continue;
    const before = tree.original(p);
    const after = tree.current(p);
    if (before === after) continue;
    rows.push({ key: p, line: before === null ? `A ${p}` : after === null ? `D ${p}` : `M ${p}` });
  }
  rows.sort((a, b) => Buffer.compare(Buffer.from(a.key, 'utf8'), Buffer.from(b.key, 'utf8')));
  if (!check) {
    for (const p of [...tree.now.keys()]) {
      const v = tree.current(p);
      if (tree.original(p) === v) continue;
      if (v === null) {
        rmSync(p, { force: true });
      } else {
        mkdirSync(dirname(p), { recursive: true });
        writeFileSync(p, v);
      }
    }
  }
  return { code: 0, out: [...rows.map((r) => r.line), `ok: ${rows.length} ${rows.length === 1 ? 'file' : 'files'}`] };
}

const trialEnv = process.env.MAKEFUN_ENV_URL;
if (trialEnv !== undefined && trialEnv !== '') {
  // A trial: the kit's runner reads the checks from the env and runs this file on each one, without this variable.
  const { runTrial } = await import('./runner.ts');
  await runTrial(trialEnv);
} else {
  const r = runCli(process.argv.slice(2));
  writeSync(1, r.out.map((l) => `${l}\n`).join(''));
  process.exitCode = r.code;
}
