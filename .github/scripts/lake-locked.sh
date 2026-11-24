#!/bin/sh
# The `lake` the authoritative workflow hands to the checker (through PEQUALNP_REAL_LAKE, the
# place tools/bin/lake reads the real lake from). The checker itself is not changed.
#
# `lake build` is the one command that compiles the proof file, and a Lean file can run code
# while it compiles. So every build runs as the account `outsider`: no network, an empty
# environment, no way to gain privileges, and write access to nothing but the output
# directories of its own module. Every other lake command (the verifier's run) is the plain
# pinned lake, run by the workflow's own account, which that compile cannot touch.
set -eu
: "${PNP_TC_BIN:?the toolchain bin directory}" "${PNP_GITCONFIG:?the git config file}"
case "${1:-}" in
  build)
    code=0
    # The whole output of the build is kept (the checker passes on only its last lines), then
    # handed to the caller unchanged, stream by stream. The directory and the two files are
    # created by THIS account, closed to every other (0700): the locked build holds only the
    # two open descriptors, as it held the caller's pipes before. It can write text into them
    # and nothing else, so their content is as untrusted as any build output.
    log=$(mktemp -d "${PNP_BUILD_LOGS:-${TMPDIR:-/tmp}}/build.XXXXXX")
    sudo -n unshare --net -- setpriv --reuid=outsider --regid=outsider --init-groups --no-new-privs \
      env -i HOME=/home/outsider LANG=C.UTF-8 PATH="$PNP_TC_BIN:/usr/bin:/bin" \
        LAKE_ARTIFACT_CACHE=false LEAN_NUM_THREADS="${PNP_LEAN_THREADS:-${LEAN_NUM_THREADS:-3}}" \
        GIT_CONFIG_GLOBAL="$PNP_GITCONFIG" GIT_CONFIG_NOSYSTEM=1 \
      "$PNP_TC_BIN/lake" "$@" > "$log/out" 2> "$log/err" || code=$?
    # Nothing a build started may outlive it: the compiled result is read only once it is still.
    sudo -n pkill -KILL -u outsider || true
    printf '%s\n' "lake $* (exit $code)" > "$log/cmd"
    cat "$log/out"; cat "$log/err" >&2
    exit "$code" ;;
  *)
    exec "$PNP_TC_BIN/lake" "$@" ;;
esac
