#!/usr/bin/env bash
# Bulletproof non-destructive backup of every live worktree into local tags wtbackup/<name>.
# Uses a TEMP index (GIT_INDEX_FILE) + commit-tree so the snapshot includes HEAD + tracked edits
# + UNTRACKED files, WITHOUT ever touching the worktree's real index/working tree. Tags are permanent
# refs => nothing can be lost to GC/prune. Idempotent (tag -f).
set -u
cd /home/dh/repo/freyd || exit 1
tmp="${TMPDIR:-/tmp}/wtbackup.idx"
git worktree list --porcelain | awk '/^worktree /{print $2}' | while read -r wt; do
  [ "$wt" = "/home/dh/repo/freyd" ] && continue
  [ -d "$wt" ] || continue
  dirty=$(git -C "$wt" status --porcelain 2>/dev/null | grep -c .)
  ahead=$(git -C "$wt" rev-list --count master..HEAD 2>/dev/null)
  [ "${dirty:-0}" -eq 0 ] && [ "${ahead:-0}" -eq 0 ] && continue
  name=$(basename "$wt")
  rm -f "$tmp"
  GIT_INDEX_FILE="$tmp" git -C "$wt" read-tree HEAD 2>/dev/null
  GIT_INDEX_FILE="$tmp" git -C "$wt" add -A 2>/dev/null
  tree=$(GIT_INDEX_FILE="$tmp" git -C "$wt" write-tree 2>/dev/null)
  rm -f "$tmp"
  if [ -n "$tree" ]; then
    snap=$(git -C "$wt" commit-tree "$tree" -p HEAD -m "wtbackup $name (HEAD+tracked+untracked)" 2>/dev/null)
  else
    snap=$(git -C "$wt" rev-parse HEAD 2>/dev/null)
  fi
  git tag -f "wtbackup/$name" "$snap" >/dev/null 2>&1
  printf 'backed up  %-38s head=%s dirty=%s ahead=%s -> wtbackup/%s (%s)\n' \
    "$name" "$(git -C "$wt" rev-parse --short HEAD)" "$dirty" "$ahead" "$name" "$(git rev-parse --short "$snap")"
done
