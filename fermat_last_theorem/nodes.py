"""Needs Python 3.9+"""
from dataclasses import dataclass, field
import json

@dataclass
class Node:
    name: str
    """The name of the node, e.g., 'FermatLastTheorem'."""
    inputs: list[str] = field(default_factory=list)
    """List of input node names, which can be used as hypotheses in the formal proof."""
    type: str = "theorem"
    """Type of the node, either 'theorem', 'definition', or 'hypothesis'."""
    informal: str = ""
    """Informal description of the theorem or concept."""
    formal: str = ""
    """Formal statement of the theorem or definition, using Lean 4 syntax."""
    informal_proof: str = ""
    """Natural language proof of the theorem, blank if the node is a definition or hypothesis."""


def load_nodes_from_json(filename):
    with open(filename, "r", encoding="utf-8") as f:
        data = json.load(f)
    # If the file contains a list of nodes
    if isinstance(data, list):
        nodes = [Node(**item) for item in data]
    # If the file contains a single node (dict)
    else:
        nodes = [Node(**data)]
    return nodes


if __name__ == "__main__":
    nodes = load_nodes_from_json("blueprint.json")

    num_nodes = len(nodes)
    print(f"Total number of nodes: {num_nodes}")

    hypothesis_count = sum(node.type == "hypothesis" for node in nodes)
    print(f"Total number of hypotheses: {hypothesis_count}")

    sorry_count = sum(node.formal.count("sorry") for node in nodes)
    print(f"Total occurrences of 'sorry' in formal statements: {sorry_count}")

    for node in nodes:
        print(f"Name: {node.name}")
        print(f"Dependencies: {node.inputs}")
        print(f"Formal statement:\n{node.formal}\n")

