"""Bounded event waits for tests.

Every wait ends on the event it names: a barrier releasing, a flag being set,
a call returning. HANG_GUARD only bounds a hang. Reaching it fails the test
with the name of the event that never came; it never decides a pass.
"""
import contextvars
import os
import stat
import threading

HANG_GUARD = 120  # seconds: generous, because a passing run never waits on it

# Bound at import: a test may patch os.open, and releasing a blocked FIFO reader
# must not go through that patch.
_open, _stat, _close = os.open, os.stat, os.close


class HangGuard(AssertionError):
    """An awaited event did not happen within HANG_GUARD."""


def hang(event):
    return HangGuard(f"{event} did not happen within {HANG_GUARD} s")


def arrive(barrier, event):
    """Wait at a threading or multiprocessing barrier, whose release is the event."""
    try:
        barrier.wait(HANG_GUARD)
    except threading.BrokenBarrierError:
        raise hang(event) from None


def await_set(flag, event):
    """Wait for a threading or multiprocessing Event to be set."""
    if not flag.wait(HANG_GUARD):
        raise hang(event)


def release_fifo_reader(path):
    """Let an open() blocked on reading the FIFO at path return: open and close its write end."""
    try:
        if stat.S_ISFIFO(_stat(path).st_mode):
            _close(_open(path, os.O_WRONLY | os.O_NONBLOCK))
    except OSError:
        pass


def returns(function, *args, event, fifos=()):
    """Call function(*args) in a thread and wait for it to return, as an event.

    Returns the result or re-raises the call's own exception. If the call has not
    returned within HANG_GUARD, it is taken to be blocked: each FIFO in fifos is
    released so a blocked open() can return, the thread is given HANG_GUARD more to
    finish, and the hang failure is raised (so a hang costs up to 2 x HANG_GUARD).
    """
    done, outcome = threading.Event(), {}
    context = contextvars.copy_context()

    def run():
        try:
            outcome["result"] = context.run(function, *args)
        except BaseException as error:  # handed back to the caller below
            outcome["error"] = error
        finally:
            done.set()

    worker = threading.Thread(target=run, daemon=True)
    worker.start()
    if not done.wait(HANG_GUARD):
        for path in fifos:
            release_fifo_reader(path)
        worker.join(HANG_GUARD)
        raise hang(event)
    worker.join()
    if "error" in outcome:
        raise outcome["error"]
    return outcome["result"]
