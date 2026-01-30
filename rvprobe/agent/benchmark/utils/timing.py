"""
Timing utilities for measuring execution time.
"""

import time
from contextlib import contextmanager
from typing import Dict


class Timer:
    """
    Simple timer for measuring elapsed time.

    Usage:
        timer = Timer()
        timer.start()
        # ... do work ...
        elapsed = timer.stop()
    """

    def __init__(self):
        self.start_time = None
        self.end_time = None
        self.elapsed = 0.0

    def start(self):
        """Start the timer."""
        self.start_time = time.time()
        self.end_time = None
        self.elapsed = 0.0

    def stop(self) -> float:
        """
        Stop the timer and return elapsed time in seconds.

        Returns:
            Elapsed time in seconds
        """
        if self.start_time is None:
            raise RuntimeError("Timer not started")

        self.end_time = time.time()
        self.elapsed = self.end_time - self.start_time
        return self.elapsed

    def reset(self):
        """Reset the timer."""
        self.start_time = None
        self.end_time = None
        self.elapsed = 0.0

    @property
    def is_running(self) -> bool:
        """Check if timer is currently running."""
        return self.start_time is not None and self.end_time is None


@contextmanager
def time_block(name: str = "Block", verbose: bool = False):
    """
    Context manager for timing a block of code.

    Usage:
        with time_block("my_operation") as timer:
            # ... do work ...
        print(f"Elapsed: {timer.elapsed}s")

    Args:
        name: Name of the block (for logging)
        verbose: If True, print timing info when exiting

    Yields:
        Timer object
    """
    timer = Timer()
    timer.start()

    try:
        yield timer
    finally:
        elapsed = timer.stop()
        if verbose:
            print(f"⏱️  [{name}] Elapsed: {elapsed:.3f}s")


class MultiTimer:
    """
    Timer for tracking multiple named intervals.

    Usage:
        mt = MultiTimer()
        mt.start("phase1")
        # ... work ...
        mt.stop("phase1")
        mt.start("phase2")
        # ... work ...
        mt.stop("phase2")
        print(mt.get_all())  # {'phase1': 1.234, 'phase2': 2.345}
    """

    def __init__(self):
        self.timers: Dict[str, Timer] = {}
        self.results: Dict[str, float] = {}

    def start(self, name: str):
        """Start a named timer."""
        if name not in self.timers:
            self.timers[name] = Timer()
        self.timers[name].start()

    def stop(self, name: str) -> float:
        """
        Stop a named timer and return elapsed time.

        Args:
            name: Timer name

        Returns:
            Elapsed time in seconds

        Raises:
            KeyError: If timer not found
        """
        if name not in self.timers:
            raise KeyError(f"Timer '{name}' not found")

        elapsed = self.timers[name].stop()
        self.results[name] = elapsed
        return elapsed

    def get(self, name: str) -> float:
        """
        Get elapsed time for a named timer.

        Args:
            name: Timer name

        Returns:
            Elapsed time in seconds, or 0.0 if not recorded
        """
        return self.results.get(name, 0.0)

    def get_all(self) -> Dict[str, float]:
        """Get all recorded times as a dictionary."""
        return self.results.copy()

    def reset(self, name: str = None):
        """
        Reset a specific timer or all timers.

        Args:
            name: Timer name to reset, or None to reset all
        """
        if name is None:
            self.timers.clear()
            self.results.clear()
        else:
            if name in self.timers:
                self.timers[name].reset()
            if name in self.results:
                del self.results[name]

    def __repr__(self) -> str:
        """String representation showing all timings."""
        if not self.results:
            return "MultiTimer(no results)"

        lines = ["MultiTimer:"]
        for name, elapsed in self.results.items():
            lines.append(f"  {name}: {elapsed:.3f}s")
        return "\n".join(lines)


def format_time(seconds: float) -> str:
    """
    Format seconds into human-readable string.

    Args:
        seconds: Time in seconds

    Returns:
        Formatted string (e.g., "1.234s", "2m 30.5s", "1h 15m 30s")
    """
    if seconds < 60:
        return f"{seconds:.3f}s"
    elif seconds < 3600:
        mins = int(seconds // 60)
        secs = seconds % 60
        return f"{mins}m {secs:.1f}s"
    else:
        hours = int(seconds // 3600)
        mins = int((seconds % 3600) // 60)
        secs = seconds % 60
        return f"{hours}h {mins}m {secs:.0f}s"
