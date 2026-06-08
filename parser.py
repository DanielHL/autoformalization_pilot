import re
import json
import sys
import warnings
from pathlib import Path
from dataclasses import dataclass, field

@dataclass
class Node:
    name: str = ""
    inputs: list[str] = field(default_factory=list)
    type: str = "theorem"
    natural: str = ""
    NL_proof: str = ""
    formal: str = ""
    """
    name:     The name of the node, e.g., 'FermatLastTheorem'.
    inputs:   List of input node names, which can be used as hypotheses in the formal proof.
    type:     Type of the node: 'theorem', 'definition', 'proposition', or 'hypothesis'.
    natural:  Natural language description of the theorem or concept.
    NL_proof: Natural language proof of the theorem; blank for definitions/hypotheses.
    formal:   Formal Lean 4 statement of the theorem or definition.
    """

def parse_lean_file(file_path: str) -> list[Node]:
    content = Path(file_path).read_text()
    nodes = []

    # Find all /-! NODE ... -/ doc blocks, paired correctly.
    # Warn on any /-! NODE that is not closed before the next one or EOF.
    block_pattern = re.compile(r'/\-! NODE(.*?)-/', re.DOTALL)
    open_pattern  = re.compile(r'/\-! NODE')

    block_matches = list(block_pattern.finditer(content))
    open_matches  = list(open_pattern.finditer(content))

    if len(open_matches) > len(block_matches):
        # At least one /-! NODE was never closed
        closed_starts = {m.start() for m in block_matches}
        for om in open_matches:
            if om.start() not in closed_starts:
                line_no = content[:om.start()].count('\n') + 1
                warnings.warn(f"Unclosed /-! NODE block starting at line {line_no}")

    for i, m in enumerate(block_matches):
        block = m.group(1)

        def get_field(pattern, default=""):
            # Each field runs from its keyword up to the next \ keyword or end of block
            match = re.search(pattern, block, re.DOTALL)
            return match.group(1).strip() if match else default

        name     = get_field(r'\\name:\s*(.+?)(?=\s*\\|\Z)')
        type_    = get_field(r'\\type:\s*(.+?)(?=\s*\\|\Z)', default="theorem")
        natural  = get_field(r'\\natural:\s*(.+?)(?=\s*\\|\Z)')
        nl_proof = get_field(r'\\NL_proof:\s*(.+?)(?=\Z)')

        inputs_raw = get_field(r'\\inputs:\s*(\[.*?\])', default="[]")
        try:
            inputs = json.loads(inputs_raw)
        except json.JSONDecodeError:
            warnings.warn(f"Could not parse \\inputs in node '{name}'; defaulting to []")
            inputs = []

        # formal: Lean code between end of this doc block and start of next /-! NODE (or EOF)
        formal_start = m.end()
        if i + 1 < len(block_matches):
            formal_end = block_matches[i + 1].start()
        else:
            formal_end = len(content)
        formal = content[formal_start:formal_end].strip()

        nodes.append(Node(name=name, inputs=inputs, type=type_,
                          natural=natural, NL_proof=nl_proof, formal=formal))

    return nodes

def main():
    if len(sys.argv) != 2:
        print("Usage: python parser.py <lean_file_path>")
        sys.exit(1)

    lean_file = Path(sys.argv[1])
    if not lean_file.exists():
        print(f"Error: File '{lean_file}' does not exist.")
        sys.exit(1)

    nodes = parse_lean_file(str(lean_file))

    json_file_path = lean_file.with_suffix('.json')
    with open(json_file_path, 'w') as json_file:
        json.dump([node.__dict__ for node in nodes], json_file, indent=4)

    print(f"Nodes have been saved to '{json_file_path}'.")
    print(f"Total number of nodes: {len(nodes)}")

    hypothesis_count = sum(node.type == "hypothesis" for node in nodes)
    print(f"Total number of hypotheses: {hypothesis_count}")

    sorry_count = sum(node.formal.count("sorry") for node in nodes)
    print(f"Total occurrences of 'sorry' in formal statements: {sorry_count}")

    for node in nodes:
        if node.formal.count("sorry") > 0:
            print(node.formal)
            print()

if __name__ == "__main__":
    main()
