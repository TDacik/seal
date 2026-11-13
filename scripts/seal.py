#!/usr/bin/env python3

import os
import sys
import argparse

from enum import StrEnum
from subprocess import run, TimeoutExpired, PIPE, STDOUT

SELF = os.path.dirname(os.path.realpath(__file__))
SV_COMP_MODE = False

OPAM_SYMLINK = "/tmp/_opam"
OPAM_PATH = os.path.join(SELF, "_opam")
FRAMAC_BIN = os.path.join(SELF, "_opam/bin/frama-c")

## New

class Verdict(StrEnum):
    OK = "ok"
    INVALID_DEREF = "invalid-deref"
    INVALID_FREE = "invalid-free"
    INVALID_MEMTRACK = "invalid-memtrack"
    ASSERTION_VIOLATION = "assertion-violated"

class Runner:
    def __init__(self, sv_comp_mode=False, debug=False):
        self.sv_comp_mode = sv_comp_mode or SV_COMP_MODE
        self.debug = debug

        if self.sv_comp_mode:
            self.framac_path = os.path.join(SELF, "_opam/bin/frama-c")
            return

        # Normal mode
        self.framac_path = "frama-c"

    def read_verdict(self, output):
        if "Invalid_free" in output:
            return Verdict.INVALID_FREE
        if "Invalid_deref" in output:
            return Verdict.INVALID_DEREF
        if "Memory_leak" in output:
            return Verdict.INVALID_MEMTRACK
        if "Assertion violated" in output:
            return Verdict.ASSERTION_VIOLATION
        if "Successful_verification" in output:
            return Verdict.OK

    def verdict_is_true(self, output):
        return self.read_verdict(output) == Verdict.OK

    def run_once(self, sources, options=[], result_filter=None, timeout=None):
        cmd = [
            self.framac_path,
            "-seal",
            "-seal-svcomp-mode",
            "-seal-no-catch-exceptions",
            *sources,
            *options
        ]

        print("[SV-wrapper] Running Frama-C with command: ", " ".join(cmd))
        sys.stdout.flush()

        try:
            process = run(cmd, timeout=timeout, stdout=PIPE, stderr=STDOUT, universal_newlines=True)
        except TimeoutExpired as to:
            return None, ""

        res = self.verdict_is_true(process.stdout)
        if result_filter is None or result_filter == res:
            return res, process.stdout

        return None, process.stdout

    def run(self, sources):
        # Try verification without abstraction
        options1 = ["-seal-abstraction", "none"]
        res1, output1 = self.run_once(sources, options=options1, timeout=5)
        if res1 is not None:
            print(output1, end="")
            return

        # Try with abstraction
        res2, output2 = self.run_once(sources, result_filter=True)
        if res2 is not None:
            print(output2, end="")
            return

        print("Inconclusive")


    def print_version():
        cmd = [FRAMAC_BIN, "-seal-version"]
        exit(run(cmd))

    def setup(self):
        """
        We need to create symlink to _opam in /tmp to deal with absolute paths".
        """
        if self.sv_comp_mode or SV_COMP_MODE:
            if not os.path.exists(OPAM_SYMLINK):
                try:
                    os.symlink(OPAM_PATH, OPAM_SYMLINK)
                except Exception as e:
                    print("Initialization of _opam symlink failed")
                    raise e

def parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument("--version", action="store_true")
    parser.add_argument("--debug", action="store_true")
    parser.add_argument("--sv-comp", action="store_true")
    parser.add_argument("--data-model", type=str, default="ILP32")
    parser.add_argument("sources", nargs="*")
    return parser.parse_args()


def main():
    args = parse_args()
    runner = Runner(sv_comp_mode=args.sv_comp, debug=args.debug)
    runner.setup()

    if args.version:
        runner.print_version()

    exit(runner.run(args.sources))

if __name__ == "__main__":
    main()

