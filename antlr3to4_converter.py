#!/usr/bin/env python3
"""
Comprehensive ANTLR3 to ANTLR4 grammar converter for yasmv
"""

import re
import sys
import os

class ANTLR3to4Converter:
    def __init__(self):
        self.scope_vars = {}  # Track scope variables for conversion
        self.current_rule = None

    def convert_file(self, input_path, output_path):
        """Convert an ANTLR3 grammar file to ANTLR4 format"""
        with open(input_path, 'r') as f:
            content = f.read()

        # Apply conversions in order
        content = self.remove_options_block(content)
        content = self.convert_header_sections(content)
        content = self.convert_scopes_to_locals(content)
        content = self.convert_scope_references(content)
        content = self.convert_returns_syntax(content)
        content = self.convert_lexer_rules(content)
        content = self.convert_actions(content)
        content = self.fix_cpp_integration(content)
        content = self.remove_syntactic_predicates(content)

        with open(output_path, 'w') as f:
            f.write(content)

    def remove_options_block(self, content):
        """Remove ANTLR3-specific options block"""
        return re.sub(r'options\s*\{[^}]*\}\s*', '', content, flags=re.DOTALL)

    def convert_header_sections(self, content):
        """Update header sections for ANTLR4"""
        # For C++ target, we need to be more careful with the members section
        content = re.sub(r'@members\s*\{', '@parser::members {', content)
        return content

    def convert_scopes_to_locals(self, content):
        """Convert ANTLR3 scope blocks to ANTLR4 locals"""
        def convert_scope(match):
            rule_name = match.group(1)
            scope_content = match.group(2)

            # Parse scope variables
            self.scope_vars[rule_name] = []
            lines = scope_content.strip().split('\n')
            local_vars = []

            for line in lines:
                line = line.strip()
                if line and not line.startswith('//'):
                    # Extract variable declaration
                    if ';' in line:
                        line = line.rstrip(';')
                    local_vars.append(line)
                    # Extract variable name for tracking
                    parts = line.split()
                    if len(parts) >= 2:
                        var_name = parts[-1].rstrip(';')
                        self.scope_vars[rule_name].append(var_name)

            if local_vars:
                locals_block = 'locals [\n    ' + ';\n    '.join(local_vars) + ';\n]'
                return f"{rule_name}\n{locals_block}"
            return rule_name

        # First, handle rule-level scopes
        pattern = r'(\w+)\s*\nscope\s*\{([^}]*)\}'
        content = re.sub(pattern, convert_scope, content, flags=re.DOTALL)

        # Also handle inline scopes
        pattern = r'(\w+)\s*scope\s*\{([^}]*)\}'
        content = re.sub(pattern, convert_scope, content, flags=re.DOTALL)

        return content

    def convert_scope_references(self, content):
        """Convert $scope::var references to ANTLR4 syntax"""
        # Convert $rule::var to $var (locals are directly accessible)
        content = re.sub(r'\$(\w+)::(\w+)', r'$\2', content)

        # Special case for global scope references like $smv::current_module
        content = re.sub(r'\$smv::current_module', 'getCurrentModule()', content)

        return content

    def convert_returns_syntax(self, content):
        """Update returns syntax if needed"""
        # ANTLR4 uses the same returns syntax, but we need to ensure proper spacing
        content = re.sub(r'returns\s*\[', 'returns [', content)
        return content

    def convert_lexer_rules(self, content):
        """Convert lexer-specific syntax"""
        # Convert channel assignments
        content = re.sub(r'\$channel\s*=\s*HIDDEN;', '-> channel(HIDDEN)', content)

        # Fix token text access
        content = re.sub(r'\$(\w+)\.text->chars', r'$\1.text', content)

        # Convert greedy operators in strings
        content = re.sub(r"'\.+'", "'.*?'", content)

        return content

    def convert_actions(self, content):
        """Convert action syntax"""
        # Update result assignments
        content = re.sub(r'\$(\w+)\s*=\s*', r'$\1.res = ', content)

        # Fix context access in actions
        content = re.sub(r'(\w+)->value\(\)', r'$\1.res->value()', content)

        return content

    def fix_cpp_integration(self, content):
        """Fix C++ specific integration issues"""
        # Add necessary using declarations if not present
        if 'using namespace' not in content:
            header_end = content.find('@parser::members')
            if header_end == -1:
                header_end = content.find('@members')

            if header_end > 0:
                using_statements = '''
using namespace std;
using namespace expr;
using namespace model;
using namespace type;
using namespace opts;
using namespace cmd;
'''
                content = content[:header_end] + using_statements + '\n' + content[header_end:]

        # Convert singleton access to function calls
        members_section = re.search(r'@parser::members\s*\{([^}]*)\}', content, re.DOTALL)
        if members_section:
            members = members_section.group(1)
            # Convert singleton declarations to methods
            members = re.sub(r'expr::ExprMgr&\s+em\s*\([^)]*\);',
                           'expr::ExprMgr& em() { return expr::ExprMgr::INSTANCE(); }', members)
            members = re.sub(r'model::ModelMgr&\s+mm\s*\([^)]*\);',
                           'model::ModelMgr& mm() { return model::ModelMgr::INSTANCE(); }', members)
            members = re.sub(r'type::TypeMgr&\s+tm\s*\([^)]*\);',
                           'type::TypeMgr& tm() { return type::TypeMgr::INSTANCE(); }', members)
            members = re.sub(r'opts::OptsMgr&\s+om\s*\([^)]*\);',
                           'opts::OptsMgr& om() { return opts::OptsMgr::INSTANCE(); }', members)
            members = re.sub(r'cmd::CommandMgr&\s+cm\s*\([^)]*\);',
                           'cmd::CommandMgr& cm() { return cmd::CommandMgr::INSTANCE(); }', members)

            content = re.sub(r'@parser::members\s*\{[^}]*\}',
                           f'@parser::members {{{members}}}', content, flags=re.DOTALL)

        return content

    def remove_syntactic_predicates(self, content):
        """Remove ANTLR3 syntactic predicates"""
        # Remove (...)=> patterns
        content = re.sub(r'\([^)]+\)\s*=>', '', content)
        return content

def main():
    converter = ANTLR3to4Converter()

    input_file = "/home/markus/src/yasmv/src/parser/grammars/smv.g"
    output_file = "/home/markus/src/yasmv/src/parser/grammars/smv.g4"

    print(f"Converting {input_file} to ANTLR4 format...")
    converter.convert_file(input_file, output_file)
    print(f"Conversion complete. Output written to {output_file}")
    print("\nPlease review the converted file for:")
    print("- Complex action blocks that may need manual adjustment")
    print("- C++ integration code")
    print("- Rule parameters and returns values")
    print("\nYou may also need to update:")
    print("- Build system to use ANTLR4")
    print("- Parser integration code to use ANTLR4 runtime")

if __name__ == "__main__":
    main()
