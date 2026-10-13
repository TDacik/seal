import argparse
import hashlib
import uuid

from pathlib import Path
from datetime import datetime, timezone


def parse_args():
    parser = argparse.ArgumentParser()

    parser.add_argument(
        "source_file",
        help="source_file",
    )

    parser.add_argument(
        "--data-model",
        type=str,
        default="ILP32",
        help="Specify data model",
    )

    parser.add_argument(
        "-f",
        "--force",
        action="store_true",
        help="Rewrite the witness if it exists",
    )

    return parser.parse_args()


def load_template():
    path = Path(__file__).resolve().parent / "template.yml"
    return path.read_text()


def gen_uuid():
    return str(uuid.uuid4())


def current_time():
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def run(args):
    template = load_template()

    while "$UUID" in template:
        template = template.replace("$UUID", gen_uuid(), 1)

    while "$TIME" in template:
        template = template.replace("$TIME", current_time(), 1)

    path = Path(args.source_file)
    content = path.read_text()
    h = hashlib.sha256(content.encode("utf-8")).hexdigest()

    template = template.replace("$DATA_MODEL", args.data_model)
    template = template.replace("$PATH", "./" + str(path))
    template = template.replace("$HASH", h)

    target = str(path).replace(".c", ".yml")

    mode = "w" if args.force else "x"

    with open(target, mode) as f:
        f.write(template)


def main():
    args = parse_args()
    run(args)


if __name__ == "__main__":
    main()
