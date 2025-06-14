import re
import json
import sys
from pathlib import Path
from dataclasses import dataclass, field

@dataclass
class Node:
    name: str
    """The name of the node, e.g., 'FermatLastTheorem'."""
    inputs: list[str] = field(default_factory=list)
    """List of input node names, which can be used as hypotheses in the formal proof."""
    type: str = "theorem"
    """Type of the node, either 'theorem', 'definition', or 'hypothesis'."""
    natural: str = ""
    """natural description of the theorem or concept."""
    formal: str = ""
    """Formal statement of the theorem or definition, using Lean 4 syntax."""
    NL_proof: str = ""
    """Natural language proof of the theorem, blank if the node is a definition or hypothesis."""

def parse_lean_file(file_path: str) -> list[Node]:
    nodes = []
    with open(file_path, 'r') as file:
        content = file.read()

    # Split content into sections based on "/-! NODE"
    node_sections = re.split(r'/-! NODE', content)[1:]  # Skip the first split part (before the first node)

    for section in node_sections:
        # Extract fields using regex
        name_match = re.search(r'\\name:\s*(.+)', section)
        inputs_match = re.search(r'\\inputs:\s*(\[[^\]]*\])', section)  # Match JSON-like list
        type_match = re.search(r'\\type:\s*(.+)', section)
        natural_match = re.search(r'\\natural:\s*(.+)', section)
        NL_proof_match = re.search(r'\\NL_proof:\s*(.+)', section)
        formal_match = re.search(r'-/(.+?)(?=/\-! NODE|$)', section, re.DOTALL)

        # Populate Node fields
        name = name_match.group(1).strip() if name_match else ""
        inputs = json.loads(inputs_match.group(1)) if inputs_match else []  # Parse as a Python list
        type = type_match.group(1).strip() if type_match else "theorem"
        natural = natural_match.group(1).strip() if natural_match else ""
        NL_proof = parse_NL_proof(section)  # Use the new function to extract natural proof
        formal = formal_match.group(1).strip() if formal_match else ""

        # Update the parser logic to strip leading and trailing spaces and newline characters for `formal` and `natural` fields
        formal = formal.strip() if formal else ""
        natural = natural.strip() if natural else ""

        # Create Node object and add to list
        nodes.append(Node(name=name, inputs=inputs, type=type, natural=natural, formal=formal, NL_proof=NL_proof))

    return nodes

def parse_NL_proof(content):
    """Extracts the full natural proof text between \\NL_proof: and -/."""
    start = content.find("\\NL_proof:")
    if start == -1:
        return None
    start += len("\\NL_proof:")
    end = content.find("-/", start)
    if end == -1:
        return None
    return content[start:end].strip()

def main():
    if len(sys.argv) != 2:
        print("Usage: python parser.py <lean_file_path>")
        sys.exit(1)

    lean_file_path = sys.argv[1]
    lean_file = Path(lean_file_path)

    if not lean_file.exists():
        print(f"Error: File '{lean_file_path}' does not exist.")
        sys.exit(1)

    # Parse the Lean file
    nodes = parse_lean_file(lean_file_path)

    # Save nodes to a JSON file
    json_file_path = lean_file.with_suffix('.json')
    with open(json_file_path, 'w') as json_file:
        json.dump([node.__dict__ for node in nodes], json_file, indent=4)

    print(f"Nodes have been saved to '{json_file_path}'.")

    num_nodes = len(nodes)
    print(f"Total number of nodes: {num_nodes}")

    hypothesis_count = sum(node.type == "hypothesis" for node in nodes)
    print(f"Total number of hypotheses: {hypothesis_count}")

    sorry_count = sum(node.formal.count("sorry") for node in nodes)
    print(f"Total occurrences of 'sorry' in formal statements: {sorry_count}")

    for node in nodes:
        print(node.formal)
        print("\n")

if __name__ == "__main__":
    main()