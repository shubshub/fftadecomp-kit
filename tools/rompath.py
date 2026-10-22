"""Find the ROM the project is built against.

The ROM is Square's data and is gitignored, so it lives on each machine under
whatever name the owner gave it.  It used to have to be called baserom.bin,
which meant a copy had to be made for anything else - a dump named for its
region, say.  Nothing about the tools needs that name, so they resolve it
instead:

    1. $FFTA_ROM, if set - an explicit path must exist and always wins;
    2. baserom.bin in the repository root, if it is there;
    3. otherwise the single .gba in the repository root.

If there is more than one .gba and no baserom.bin, that is ambiguous and the
caller is told so rather than being handed a coin toss.
"""
import os


def rom_candidates(root):
    """every plausible ROM in the repository root, in preference order"""
    out = []
    env = os.environ.get("FFTA_ROM")
    if env:
        out.append(env if os.path.isabs(env) else os.path.join(root, env))
    out.append(os.path.join(root, "baserom.bin"))
    try:
        for name in sorted(os.listdir(root)):
            if name.lower().endswith(".gba"):
                out.append(os.path.join(root, name))
    except OSError:
        pass
    return out


def rom_path(root=".", required=True):
    """Resolve one ROM; optional absence is allowed, invalid selection is not."""
    root = os.path.abspath(root)
    env = os.environ.get("FFTA_ROM")
    if env:
        path = env if os.path.isabs(env) else os.path.join(root, env)
        if os.path.isfile(path):
            return path
        raise SystemExit(f"FFTA_ROM does not name a ROM file: {path}")
    baseline = os.path.join(root, "baserom.bin")
    if os.path.isfile(baseline):
        return baseline
    gbas = [path for path in rom_candidates(root)
            if path.lower().endswith(".gba") and os.path.isfile(path)]
    if len(gbas) > 1:
        raise SystemExit(
            f"more than one .gba in {root} and no baserom.bin:\n  " +
            "\n  ".join(os.path.basename(p) for p in gbas) +
            "\nSet $FFTA_ROM to the one to use.")
    if gbas:
        return gbas[0]
    if not required:
        return None
    raise SystemExit(
        f"no ROM in {root}.  Put the .gba there, or set $FFTA_ROM to its path.")


def rom_name(path):
    """the name a ROM should be copied to inside a scratch tree"""
    return "baserom.bin"
