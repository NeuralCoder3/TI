s="""#!/bin/python3
def get_code():
    import base64
    selfref = 'QUINIFY'
    return base64.b64decode(selfref).decode('utf-8').replace('QUINIFY', selfref, 1)

print(get_code(), end='')

"""

program="hello.py"

s+=open(program).read()

import base64

code=base64.b64encode(s.encode('utf-8')).decode('utf-8')
program=s.replace("selfref = 'QUINIFY'","selfref = '"+code+"'")
print(program)

#test: python quinegen.py > t.py && python t.py && echo -e "\n" && cat t.py
