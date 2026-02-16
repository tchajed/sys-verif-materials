import os
import re

def apply_replacements(content):
    # 1. replace IsPkgInit with IsPkgInit (iProp Σ)
    content = re.sub(r'\bIsPkgInit\b(?!\s*\(iProp Σ\))', r'IsPkgInit (iProp Σ)', content)
    
    # 2. replace GetIsPkgInitWf with GetIsPkgInitWf (iProp Σ)
    content = re.sub(r'\bGetIsPkgInitWf\b(?!\s*\(iProp Σ\))', r'GetIsPkgInitWf (iProp Σ)', content)
    
    # 3. replace ADDR ↦s[ GO_TYPE :: "FIELDNAME" ] with ADDR.[GO_TYPE.t, "FIELDNAME"] ↦
    def fix_mapsto(match):
        addr = match.group(1)
        go_type = match.group(2).strip()
        fieldname = match.group(3).strip()
        return f'{addr}.[{go_type}.t, "{fieldname}"] ↦'
    
    content = re.sub(r'(\S+)\s*↦s\[\s*([^:]+)\s*::\s*"([^"]+)"\s*\]', fix_mapsto, content)
    
    # 4. replace wp_pures with wp_auto.
    content = re.sub(r'\bwp_pures\b', r'wp_auto', content)
    
    # 5. replace  @  with  @!  (only when there are spaces though, not all @ should be replaced)
    content = re.sub(r' @ ', r' @! ', content)
    
    # 6. replace ptrT.id with go.PointerType
    content = re.sub(r'\bptrT\.id\b', r'go.PointerType', content)
    
    # 7. replace someType.id with someType
    content = re.sub(r'(\b[\w\.]+\b)\.id', r'\1', content)
    
    return content

def main():
    for root, dirs, files in os.walk('.'):
        for file in files:
            if file.endswith('.v'):
                path = os.path.join(root, file)
                with open(path, 'r', encoding='utf-8') as f:
                    content = f.read()
                
                new_content = apply_replacements(content)
                
                if new_content != content:
                    with open(path, 'w', encoding='utf-8') as f:
                        f.write(new_content)
                    print(f"Updated {path}")

if __name__ == "__main__":
    main()
