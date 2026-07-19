#!/usr/bin/env bash
# Report each worktree's live-ness: uncommitted changes + commits not reachable from master.
set -u
cd /home/dh/repo/freyd || exit 1
git worktree list --porcelain | awk '/^worktree /{print $2}' | while read -r wt; do
  [ "$wt" = "/home/dh/repo/freyd" ] && continue
  if [ ! -d "$wt" ]; then
    printf 'GONE      %s\n' "$wt"
    continue
  fi
  head=$(git -C "$wt" rev-parse --short HEAD 2>/dev/null)
  dirty=$(git -C "$wt" status --porcelain 2>/dev/null | grep -c .)
  ahead=$(git -C "$wt" rev-list --count master..HEAD 2>/dev/null)
  if [ "${dirty:-0}" -gt 0 ] || [ "${ahead:-0}" -gt 0 ]; then
    printf 'LIVE      %s  head=%s  dirty=%s  ahead=%s\n' "$wt" "$head" "$dirty" "$ahead"
  else
    printf 'stale     %s  head=%s\n' "$wt" "$head"
  fi
done
