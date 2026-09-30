#!/bin/sh
# Shared FIFO compilation queue for this 8 GB workstation (one active compiler).
# Run from lean_wong; all arguments are passed literally to Lean.
set -eu
task_pool_dir="$PWD/.lake/campaign-lean-slots"
mkdir -p "$task_pool_dir/queue"
# Assign monotonically increasing tickets under an atomic directory lock.
while ! mkdir "$task_pool_dir/ticket-lock" 2>/dev/null; do sleep 0.2; done
task_previous_ticket=0
if [ -f "$task_pool_dir/next-ticket" ]; then
  task_previous_ticket=$(cat "$task_pool_dir/next-ticket")
fi
task_ticket_number=$((task_previous_ticket + 1))
task_ticket=$(printf '%020d' "$task_ticket_number")
mkdir "$task_pool_dir/queue/$task_ticket"
printf '%s\n' "$$" > "$task_pool_dir/queue/$task_ticket/owner-pid"
printf '%s\n' "$task_ticket_number" > "$task_pool_dir/next-ticket"
rmdir "$task_pool_dir/ticket-lock"
task_slot=""
task_cleanup() {
  rm -f "$task_pool_dir/queue/$task_ticket/owner-pid"
  rmdir "$task_pool_dir/queue/$task_ticket" 2>/dev/null || true
  if [ -n "$task_slot" ]; then
    rm -f "$task_slot/owner-pid"
    rmdir "$task_slot" 2>/dev/null || true
  fi
}
trap task_cleanup EXIT
trap 'exit 130' INT
trap 'exit 143' TERM
while [ -z "$task_slot" ]; do
  task_front=$(ls "$task_pool_dir/queue" | LC_ALL=C sort | head -n 1)
  if [ "$task_front" = "$task_ticket" ]; then
    for task_index in 1; do
      if mkdir "$task_pool_dir/$task_index" 2>/dev/null; then
        task_slot="$task_pool_dir/$task_index"
        printf '%s\n' "$$" > "$task_slot/owner-pid"
        rm -f "$task_pool_dir/queue/$task_ticket/owner-pid"
        rmdir "$task_pool_dir/queue/$task_ticket"
        break
      fi
    done
  fi
  if [ -z "$task_slot" ]; then sleep 0.5; fi
done
/Users/rinithpina/.elan/bin/lake env lean "$@"
