#!/usr/bin/env python3
"""Generate a higher-order effect-inference size probe for Yulang."""

from __future__ import annotations

import argparse


def nested_apply(depth: int) -> str:
    expr = "x"
    for _ in range(depth):
        expr = f"f ({expr})"
    return expr


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("depth", type=int, nargs="?", default=64)
    args = parser.parse_args()
    if args.depth < 0:
        parser.error("depth must be non-negative")
    print(f"pub deep_{args.depth}(f, x) = {nested_apply(args.depth)}")


if __name__ == "__main__":
    main()
