#!/usr/bin/env python3
"""Convert ANTLR3 grammar to ANTLR4 syntax"""

import re
import sys

def convert_antlr3_to_antlr4(content):
    """Convert ANTLR3 grammar syntax to ANTLR4"""

    # Remove options block
    content = re.sub(r'options\s*\{[^}]*\}', '', content, flags=re.DOTALL)

    # Convert scope blocks to locals
    # scope { ... } -> locals [ ... ]
    content = re.sub(r'scope\s*\{([^}]*)\}', r'locals [\1]', content)

    # Convert scope variable references
    # $rule::var -> $ctx.var or local var access
    content = re.sub(r'\$(\w+)::(\w+)', r'$\1.ctx.\2', content)

    # Fix member variable access in actions
    # For rules like $smv::current_module, we need special handling
    content = re.sub(r'\$smv\.ctx\.current_module', r'$ctx.current_module', content)

    # Convert returns syntax
    # returns [type name] -> returns [type name] (no change needed actually)

    # Fix channel assignment in lexer rules
    # $channel=HIDDEN; -> -> channel(HIDDEN)
    content = re.sub(r'\$channel\s*=\s*HIDDEN;', '-> channel(HIDDEN)', content)

    # Fix token text access
    # $TOKEN.text->chars -> $TOKEN.text
    content = re.sub(r'\$(\w+)\.text->chars', r'$\1.text', content)

    # Remove syntactic predicates
    # (expr) => -> just remove the =>
    content = re.sub(r'\([^)]+\)\s*=>', '', content)

    # Fix fragment rules
    # fragment RULE : ... ; -> fragment RULE : ... ;
    # (no change needed)

    # Fix string literals in lexer
    # '.+' -> '.*?' for non-greedy matching
    content = re.sub(r"'\.+'", "'.*?'", content)

    # Fix @init blocks - ensure proper C++ syntax
    # This is more complex and might need manual review

    # Fix local variable declarations in rules
    # In ANTLR4, locals need to be declared differently

    return content

def main():
    input_file = "/home/markus/src/yasmv/src/parser/grammars/smv.g"
    output_file = "/home/markus/src/yasmv/src/parser/grammars/smv_antlr4.g"

    with open(input_file, 'r') as f:
        content = f.read()

    converted = convert_antlr3_to_antlr4(content)

    with open(output_file, 'w') as f:
        f.write(converted)

    print(f"Converted grammar written to {output_file}")
    print("Note: Manual review and adjustments may be needed for:")
    print("- Complex action blocks")
    print("- Local variable declarations")
    print("- C++ integration code")

if __name__ == "__main__":
    main()
