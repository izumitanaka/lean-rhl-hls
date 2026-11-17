#!/usr/bin/env python3
"""Inspect freshly emitted C for syntax traversal's runtime recursion path.

Run lake env lean -c artifacts/structural-frontend/<Module>.c on each
frontend module first. This checks direct construction/recursion calls, not
transitive type-conversion totality and not optimization/execution budgets.
"""
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "artifacts/structural-frontend"
FORBIDDEN = re.compile(
    r"\b\w*WordFrontend_(?:syntaxSize|sourceBudget|scalar|body|stepBody)\("
    r"|\b\w*ScalarEnvironment_(?:parseCompatible|compile)\("
)
FUNCTION = re.compile(r"^LEAN_EXPORT [^\n]*?\b(\w+)\([^;\n]*\) \{\n", re.M)


def main():
    records = []
    for module, namespace, roots in [
        ("WordStructuralBody", "StructuralBody", ("node", "visit", "body", "compile", "visitRetained", "bodyRetained", "compileRetained", "retainArguments", "bindArgument", "unitArgument", "argumentAnnotation", "retargetRetainedPiece")),
        ("WordScalarEnvironment", "ScalarEnvironment", ("node", "visit", "parse")),
        ("LeanRetainedConversion", "RetainedConversion", ("reducePrefix", "conversion", "prefixLength", "automatic")),
    ]:
        c = (OUT / f"{module}.c").read_text()
        selected = re.compile(rf"WordFrontend_{namespace}_(?:{'|'.join(roots)})(?:___|$)")
        functions = []
        for start in FUNCTION.finditer(c):
            name = start[1]
            if not selected.search(name):
                continue
            end = c.find("\n}", start.end())
            assert end >= 0, name
            body = c[start.end():end]
            forbidden = FORBIDDEN.findall(body)
            assert not forbidden, (module, name, forbidden)
            functions.append(name)
        assert functions, module
        records.append({"module": module, "functions": functions, "forbidden_calls": []})
    data = {
        "status": "PASS",
        "scope": "Direct calls in new scalar/body/step traversal and structural compile",
        "not_claimed": "No claim about all fallback paths or type-conversion fuel",
        "modules": records,
    }
    (OUT / "generated-c-check.json").write_text(json.dumps(data, indent=2) + "\n")
    print(f"PASS {sum(len(x['functions']) for x in records)} generated C functions")


if __name__ == "__main__":
    main()
