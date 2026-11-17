#!/usr/bin/env python3

import os
import sys
import argparse

from enum import StrEnum
from pathlib import Path
from subprocess import run, TimeoutExpired, PIPE, STDOUT

SELF = os.path.dirname(os.path.realpath(__file__))
STANDALONE_MODE = False

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

class Property(StrEnum):
    VALID_MEMSAFETY = "valid-memsafety"
    VALID_MEMCLEANUP = "valid-memcleanup"
    UNREACH_CALL = "unreach-call"

    @staticmethod
    def from_file(path):
        name = Path(path).name
        if name == "valid-memsafety.prp":
            return Property.VALID_MEMSAFETY
        if name == "valid-memcleanup.prp":
            return Property.VALID_MEMCLEANUP
        if name == "unreach-call.prp":
            return Property.UNREACH_CALL

        print("Unknown property file")
        exit(1)

    def to_seal_param(self):
        if self is None:
            return []
        elif self == Property.VALID_MEMSAFETY:
            prop = "mem-safety"
        elif self == Property.VALID_MEMCLEANUP:
            prop = "mem-cleanup"
        elif self == Property.UNREACH_CALL:
            prop = "assertions"
        else:
            assert False
        return [f"-seal-check={prop}"]

class Runner:
    def __init__(self, args):
        self.sv_comp_mode = args.sv_comp
        self.debug = args.debug
        self.machdep = args.machdep
        if args.property_file:
            self.property = Property.from_file(args.property_file)
        else:
            self.property = None

        if self.sv_comp_mode:
            self.framac_path = os.path.join(SELF, "_opam/bin/frama-c")
            return

        # Normal mode
        self.framac_path = "frama-c"

    def log_info(self):
        if self.property:
            print(f"[Seal driver] Verifying property: {self.property}")
        else:
            print("[Seal driver] No property specified")

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
        # fmt: off
        cmd = [
            self.framac_path,
            "-seal",
            *self.property.to_seal_param(),
            "-machdep", self.machdep,
            "-seal-svcomp-mode",
            "-seal-no-catch-exceptions",
            "-seal-witness", "witness.yml",
            *sources,
            *options
        ]
        # fmt: on

        print("[Seal driver] Running Frama-C with command: ", " ".join(cmd))
        sys.stdout.flush()

        try:
            process = run(cmd, timeout=timeout, stdout=PIPE, stderr=STDOUT, universal_newlines=True)
        except TimeoutExpired as to:
            return None, ""

        res = self.verdict_is_true(process.stdout)
        if result_filter is None or result_filter == res:
            return res, process.stdout

        return None, process.stdout

    def run_verification(self, args):
        sources = args.sources

        # Try verification without abstraction
        options1 = ["-seal-abstraction", "none"]
        res1, output1 = self.run_once(sources, options=options1, timeout=15)
        if res1 is not None:
            print(output1, end="")
            return

        Path("witness.yml").unlink(missing_ok=True)

        # Try with abstraction
        res2, output2 = self.run_once(sources, result_filter=True, timeout=180)
        if res2 is not None:
            print(output2, end="")
            return

        # Try verification without abstraction
        options3 = ["-seal-abstraction", "none", "-seal-max-loop-cycles", 3]
        res3, output3 = self.run_once(sources, options=options1, result_filter=False)
        if res3 is not None:
            print(output3, end="")
            return

        Path("witness.yml").unlink(missing_ok=True)

        print("Inconclusive")

    def run_validation(self, args):
        cmd = [
            self.framac_path,
            "-seal",
            #"-machdep",
            #self.machdep,
            "-seal-abstraction=none",
            "-seal-no-memcleanup",
            f"-seal-validate-witness={args.validate_witness}",
            "-seal-svcomp-mode",
            "-seal-no-catch-exceptions",
            *args.sources,
        ]

        process = run(cmd)
        exit(process.returncode)

    def print_version(self):
        cmd = [self.framac_path, "-seal-version"]
        res = run(cmd)
        exit(res.returncode)

    def setup(self):
        """
        We need to create symlink to _opam in /tmp to deal with absolute paths".
        """
        if STANDALONE_MODE:
            if not os.path.exists(OPAM_SYMLINK):
                try:
                    os.symlink(OPAM_PATH, OPAM_SYMLINK)
                except Exception as e:
                    print("Initialization of _opam symlink failed")
                    raise e


def parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument("--version", action="store_true")
    parser.add_argument("--property-file", type=str, default=None)
    parser.add_argument("--debug", action="store_true")
    parser.add_argument("--sv-comp", action="store_true")
    parser.add_argument("--synthesis-abstraction", action="store_true")
    parser.add_argument("--validate-witness", type=str, default=None)
    parser.add_argument("-machdep", type=str, default="gcc_x86_32")
    parser.add_argument("sources", nargs="*")
    return parser.parse_args()


def main():
    args = parse_args()
    runner = Runner(args)
    runner.setup()

    if args.version:
        runner.print_version()

    runner.log_info()

    if args.validate_witness is not None:
        exit(runner.run_validation(args))
    else:
        exit(runner.run_verification(args))

if __name__ == "__main__":
    main()

