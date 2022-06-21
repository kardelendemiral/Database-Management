from fileinput import filename
import random
import sys
import time
import json
import re
import os
import math
import ast

PAGESIZE = 2000
PAGE_IN_A_FILE = 10

splits = 0
parent_splits = 0
fusions = 0
parent_fusions = 0

bTrees = {}



class Node(object):
    """Base node object. It should be index node
    Each node stores keys and children.
    Attributes:
        parent
    """

    def __init__(self, parent=None):
        """Child nodes are stored in values. Parent nodes simply act as a medium to traverse the tree.
        :type parent: Node"""
        self.keys: list = []
        self.values: list[Node] = []
        self.parent: Node = parent

    def getAddress(self, x):

        index = 0

        for i in self.keys:
            if i == x:
                adr = self.values[index]
                return adr
            index = index+1

    def index(self, key):
        """Return the index where the key should be.
        :type key: str
        """
        for i, item in enumerate(self.keys):
            if key < item:
                return i

        return len(self.keys)

    def __getitem__(self, item):
        return self.values[self.index(item)]

    def __setitem__(self, key, value):
        i = self.index(key)
        self.keys[i:i] = [key]
        self.values.pop(i)
        self.values[i:i] = value

    def split(self):
        """Splits the node into two and stores them as child nodes.
        extract a pivot from the child to be inserted into the keys of the parent.
        @:return key and two children
        """
        global splits, parent_splits
        splits += 1
        parent_splits += 1

        left = Node(self.parent)

        mid = len(self.keys) // 2

        left.keys = self.keys[:mid]
        left.values = self.values[:mid + 1]
        for child in left.values:
            child.parent = left

        key = self.keys[mid]
        self.keys = self.keys[mid + 1:]
        self.values = self.values[mid + 1:]

        return key, [left, self]

    def __delitem__(self, key):
        i = self.index(key)
        del self.values[i]
        if i < len(self.keys):
            del self.keys[i]
        else:
            del self.keys[i - 1]

    def fusion(self):
        global fusions, parent_fusions
        fusions += 1
        parent_fusions += 1

        index = self.parent.index(self.keys[0])
        # merge this node with the next node
        if index < len(self.parent.keys):
            next_node: Node = self.parent.values[index + 1]
            next_node.keys[0:0] = self.keys + [self.parent.keys[index]]
            for child in self.values:
                child.parent = next_node
            next_node.values[0:0] = self.values
        else:  # If self is the last node, merge with prev
            prev: Node = self.parent.values[-2]
            prev.keys += [self.parent.keys[-1]] + self.keys
            for child in self.values:
                child.parent = prev
            prev.values += self.values

    def borrow_key(self, minimum: int):
        index = self.parent.index(self.keys[0])
        if index < len(self.parent.keys):
            next_node: Node = self.parent.values[index + 1]
            if len(next_node.keys) > minimum:
                self.keys += [self.parent.keys[index]]

                borrow_node = next_node.values.pop(0)
                borrow_node.parent = self
                self.values += [borrow_node]
                self.parent.keys[index] = next_node.keys.pop(0)
                return True
        elif index != 0:
            prev: Node = self.parent.values[index - 1]
            if len(prev.keys) > minimum:
                self.keys[0:0] = [self.parent.keys[index - 1]]

                borrow_node = prev.values.pop()
                borrow_node.parent = self
                self.values[0:0] = [borrow_node]
                self.parent.keys[index - 1] = prev.keys.pop()
                return True

        return False


class Leaf(Node):
    def __init__(self, parent=None, prev_node=None, next_node=None):
        """
        Create a new leaf in the leaf link
        :type prev_node: Leaf
        :type next_node: Leaf
        """
        super(Leaf, self).__init__(parent)
        self.next: Leaf = next_node
        if next_node is not None:
            next_node.prev = self
        self.prev: Leaf = prev_node
        if prev_node is not None:
            prev_node.next = self

    def __getitem__(self, item):
        return self.values[self.keys.index(item)]

    def __setitem__(self, key, value):
        i = self.index(key)
        if key not in self.keys:
            self.keys[i:i] = [key]
            self.values[i:i] = [value]
        else:
            self.values[i - 1] = value

    def split(self):
        global splits
        splits += 1

        left = Leaf(self.parent, self.prev, self)
        mid = len(self.keys) // 2

        left.keys = self.keys[:mid]
        left.values = self.values[:mid]

        self.keys: list = self.keys[mid:]
        self.values: list = self.values[mid:]

        # When the leaf node is split, set the parent key to the left-most key of the right child node.
        return self.keys[0], [left, self]

    def __delitem__(self, key):
        i = self.keys.index(key)
        del self.keys[i]
        del self.values[i]

    def fusion(self):
        global fusions
        fusions += 1

        if self.next is not None and self.next.parent == self.parent:
            self.next.keys[0:0] = self.keys
            self.next.values[0:0] = self.values
        else:
            self.prev.keys += self.keys
            self.prev.values += self.values

        if self.next is not None:
            self.next.prev = self.prev
        if self.prev is not None:
            self.prev.next = self.next

    def borrow_key(self, minimum: int):
        index = self.parent.index(self.keys[0])
        if index < len(self.parent.keys) and len(self.next.keys) > minimum:
            self.keys += [self.next.keys.pop(0)]
            self.values += [self.next.values.pop(0)]
            self.parent.keys[index] = self.next.keys[0]
            return True
        elif index != 0 and len(self.prev.keys) > minimum:
            self.keys[0:0] = [self.prev.keys.pop()]
            self.values[0:0] = [self.prev.values.pop()]
            self.parent.keys[index - 1] = self.keys[0]
            return True

        return False


class BPlusTree(object):
    """B+ tree object, consisting of nodes.
    Nodes will automatically be split into two once it is full. When a split occurs, a key will
    'float' upwards and be inserted into the parent node to act as a pivot.
    Attributes:
        maximum (int): The maximum number of keys each node can hold.
    """
    root: Node

    def __init__(self, maximum=4):
        self.root = Leaf()
        self.maximum: int = maximum if maximum > 2 else 2
        self.minimum: int = self.maximum // 2
        self.depth = 0

    def find(self, key) -> Leaf:
        """ find the leaf
        Returns:
            Leaf: the leaf which should have the key
        """
        node = self.root
        # Traverse tree until leaf node is reached.
        while type(node) is not Leaf:
            node = node[key]

        return node

    def __getitem__(self, item):
        return self.find(item)[item]

    def query(self, key):
        """Returns a value for a given key, and None if the key does not exist."""
        leaf = self.find(key)
        return leaf[key] if key in leaf.keys else None

    def change(self, key, value):
        """change the value
        Returns:
            (bool,Leaf): the leaf where the key is. return False if the key does not exist
        """
        leaf = self.find(key)
        if key not in leaf.keys:
            return False, leaf
        else:
            leaf[key] = value
            return True, leaf

    def __setitem__(self, key, value, leaf=None):
        """Inserts a key-value pair after traversing to a leaf node. If the leaf node is full, split
              the leaf node into two.
              """
        if leaf is None:
            leaf = self.find(key)
        leaf[key] = value
        if len(leaf.keys) > self.maximum:
            self.insert_index(*leaf.split())

    def insert(self, key, value):
        """
        Returns:
            (bool,Leaf): the leaf where the key is inserted. return False if already has same key
        """
        leaf = self.find(key)
        if key in leaf.keys:
            return False, leaf
        else:
            self.__setitem__(key, value, leaf)
            return True, leaf

    def insert_index(self, key, values: list[Node]):
        """For a parent and child node,
                    Insert the values from the child into the values of the parent."""
        parent = values[1].parent
        if parent is None:
            values[0].parent = values[1].parent = self.root = Node()
            self.depth += 1
            self.root.keys = [key]
            self.root.values = values
            return

        parent[key] = values
        # If the node is full, split the  node into two.
        if len(parent.keys) > self.maximum:
            self.insert_index(*parent.split())
        # Once a leaf node is split, it consists of a internal node and two leaf nodes.
        # These need to be re-inserted back into the tree.

    def delete(self, key, node: Node = None):
        if node is None:
            node = self.find(key)
        del node[key]

        if len(node.keys) < self.minimum:
            if node == self.root:
                if len(self.root.keys) == 0 and len(self.root.values) > 0:
                    self.root = self.root.values[0]
                    self.root.parent = None
                    self.depth -= 1
                return

            elif not node.borrow_key(self.minimum):
                node.fusion()
                self.delete(key, node.parent)
        # Change the left-most key in node
        # if i == 0:
        #     node = self
        #     while i == 0:
        #         if node.parent is None:
        #             if len(node.keys) > 0 and node.keys[0] == key:
        #                 node.keys[0] = self.keys[0]
        #             return
        #         node = node.parent
        #         i = node.index(key)
        #
        #     node.keys[i - 1] = self.keys[0]

    def show(self, node=None, file=None, _prefix="", _last=True):
        """Prints the keys at each level."""
        if node is None:
            node = self.root
        print(_prefix, "`- " if _last else "|- ", node.keys, sep="", file=file)
        _prefix += "   " if _last else "|  "

        if type(node) is Node:
            # Recursively print the key of child nodes (if these exist).
            for i, child in enumerate(node.values):
                _last = (i == len(node.values) - 1)
                self.show(child, file, _prefix, _last)

    def output(self):
        return splits, parent_splits, fusions, parent_fusions, self.depth

    def readfile(self, reader):
        i = 0
        for i, line in enumerate(reader):
            s = line.decode().split(maxsplit=1)
            self[s[0]] = s[1]
            if i % 1000 == 0:
                print('Insert ' + str(i) + 'items')
        return i + 1

    def leftmost_leaf(self) -> Leaf:
        node = self.root
        while type(node) is not Leaf:
            node = node.values[0]
        return node


def demo():
    bplustree = BPlusTree()
    #random_list = random.sample(range(1, 100), 20)
    random_list = [1,5,2,3,4,6,7,8]
    for i in random_list:
        bplustree[i] = 'test' + str(i)
        print('Insert ' + str(i))
        bplustree.show()

    random.shuffle(random_list)
    """
     for i in random_list:
        print('Delete ' + str(i))
        bplustree.delete(i)
        bplustree.show()
    """

   # print(bplustree.find(5).getAddress(5))



def checkFileEmpty(file_name):
    
    systemCat = open("systemCatalog.csv")

    lines = systemCat.readlines()

    text = ""

    type_name = file_name[0:file_name.index("_")]
    print(type_name)

    for line in lines:
        if line[0: len(type_name)] == type_name:
            text = line
            break


    nofFields = int(text.split(",")[1])
    lengthOfARecord = int(nofFields * 20)

    f = open(file_name,"r")
    f.seek(1)
    isEmpty = False
    pageNo = 0
    byte = 0
    
    
    recordsInAPage = int(math.floor((PAGESIZE-1)/(lengthOfARecord+1)))

    for i in range(PAGE_IN_A_FILE):
        print(i)
        
        byte = byte+1
        recordHeader = f.read(1)
        recordNo = 0
        if pageNo == PAGE_IN_A_FILE-1:
                isEmpty = True
                break
        while recordHeader != "1":
            if recordNo == recordsInAPage :
                break
            print("recordheader:",recordHeader,"byte",byte)
            byte = byte + lengthOfARecord  +1
            
            f.seek(byte)
            recordHeader = f.read(1)
            recordNo = recordNo + 1
        pageNo = pageNo + 1

    return isEmpty




def createType(type_name, nof_fields, prim_key_order, fieldsAndTypes):

    x = getAllTypeNames()

    if type_name in x:
        return False
    #print("create typedayım")
    bplustree = BPlusTree()

    bTrees[type_name] = bplustree

    file = open("systemCatalog.csv", "a+")
    f = open(type_name+"_1.txt", "a+")
    btreefile = open("bTree" +type_name +".txt","a+")
    #btreefile.write("{}")

    file.write(type_name+","+str(nof_fields)+","+str(prim_key_order)+","+str(fieldsAndTypes)+","+type_name+"_1.txt"+"\n")

    nofFields = len(fieldsAndTypes)/2
    lengthOfARecord = int(nofFields * 20)
    #f.seek(0)
    #print("noffields",nofFields)
    #print("lengthofarecord",lengthOfARecord)

    nofRecords = math.floor((PAGESIZE-1) / (lengthOfARecord+1))
    #print("nofrecords",nofRecords)


    text = "0"+(" " * lengthOfARecord)

    for page in range(PAGE_IN_A_FILE):

    
        f.write("0")
        for i in range(nofRecords):
            f.write(text)

        f.write(" "*(PAGESIZE-len(text)*nofRecords - 1 ))

    file.close()
    f.close()

    return True



def createRecord(type_name, fields):

    types = getAllTypeNames()

    if type_name not in types:
        return False


    systemCat = open("systemCatalog.csv")

    lines = systemCat.readlines()

    text = ""

    for line in lines:
        if line[0: len(type_name)] == type_name:
            text = line
            break

    #print(text,end="")
    fileName = text.split(',')[-1][:-1]

    #print(fileName,end="")

    f = open(fileName, "r+")
    byte= 0
    f.seek(byte)
    processedPage = 0
    isFull = False
    pageNo = 0

    nofFields = int(text.split(",")[1])
    prim_key_order = int(text.split(",")[2])
    lengthOfARecord = int(nofFields * 20)
    recordsInAPage = int(math.floor((PAGESIZE-1)/(lengthOfARecord+1)))

    primkey = fields[int(prim_key_order)-1]
    

    if len(fields) != nofFields:
        return False

    
    
    b_tree = bTrees[type_name]
    
    leftMost = b_tree.leftmost_leaf()
    keys = []

    while leftMost is not None:
        keys.extend(leftMost.keys) 
        leftMost =  leftMost.next 
    
    if primkey in keys:
        return False
   
    updfields = ""
    for fd in fields:
        a = '{:20}'.format(fd)
        updfields = updfields + a
    

    while f.read(1) != "0":
        #print("page no", pageNo)
        if pageNo == PAGE_IN_A_FILE-1:
            isFull = True
            print("doldu")
            break
        byte = byte + PAGESIZE
        f.seek(byte)
        #print("byte nosunda bunu okuyo,",byte,":",f.read(1))
        pageNo = pageNo + 1
        #print("byte",byte)
    recordNo = 0
    if isFull == False:
        f.seek(byte+1)
        recordLocation = byte + 1
        while f.read(1) != "0":
            
            recordLocation = recordLocation + lengthOfARecord + 1
            #print("record loc",recordLocation)
            f.seek(recordLocation)
            recordNo = recordNo + 1
            #print("recordno: ",recordNo)
        f.seek(recordLocation)
        f.write("1")
        f.seek(recordLocation + 1)
        f.write(updfields)
        address = fileName + "," + str(recordLocation+1)
        #print("address:",address)
        #print("records in a page",recordsInAPage)
        if recordNo == recordsInAPage-1:
            f.seek(byte)
            f.write("1")
    else:
        f.close()
        fileno = int(re.findall("_[\d]*.txt", str(fileName))[0].split('.')[0])+1
        #print(fileno)
        newfilename = type_name + "_"+ str(fileno) +".txt"
        #print("newfilename: ",newfilename)
        newFile = open(newfilename,"w+")
        
        nofFields = len(fields)
        lengthOfARecord = int(nofFields * 20)
        recordsInAPage = int(math.floor((PAGESIZE-1)/(lengthOfARecord+1)))

        nofRecords = math.floor((PAGESIZE-1) / (lengthOfARecord+1))


        text = "0"+(" " * lengthOfARecord)

        for page in range(PAGE_IN_A_FILE):

        
            newFile.write("0")
            for i in range(nofRecords):
                newFile.write(text)

            newFile.write(" "*(PAGESIZE-len(text)*nofRecords - 1 ))
        
      
        newFile.seek(1)
        newFile.write("1")
        newFile.seek(2)
        newFile.write(updfields)
        systemCat.close()

        address = fileName + "," + str(2)

        with open('systemCatalog.csv', 'r') as cat :
            filedata = cat.read()

        # Replace the target string
        filedata = filedata.replace(fileName, newfilename)


        # Write the file out again
        with open('systemCatalog.csv', 'w') as ctlg:
            ctlg.write(filedata)

    
    b_tree = bTrees[type_name]

    primkey = fields[int(prim_key_order)-1]

    b_tree[primkey] = address

    return True

def deleteType(type_name):

    types = getAllTypeNames()

    if type_name not in types:
        return False
    
    del bTrees[type_name]

    dir_name = "./"
    test = os.listdir(dir_name)
    print(test)

    for item in test:
        if item.startswith(type_name):
            os.remove(os.path.join(dir_name, item))
    btr="bTree" + type_name + ".txt"
    os.remove(btr)

    

    with open("systemCatalog.csv", "r") as f:
        lines = f.readlines()
    with open("systemCatalog.csv", "w") as f:
        for line in lines:
            if line.split(",")[0] != type_name:
                f.write(line)


    return True

def listType(outputFile):
    
    types = getAllTypeNames()

    for type in types:
        outputFile.write(type+"\n")

    if len(types)==0:
        return False 

    return True


#BURAYA TEKRAR BAKALIM KONTROLLLLLLLLLLLLLLLL
#  
def deleteRecord(type_name, prim_key):

    

    types = getAllTypeNames()

    if type_name not in types:
        return False
    
    b_tree = bTrees[type_name]
    
    leftMost = b_tree.leftmost_leaf()
    keys = []

    while leftMost is not None:
        keys.extend(leftMost.keys) 
        leftMost =  leftMost.next 
    
    if prim_key not in keys:
        return False
    
    

    address = bTrees[type_name].find(prim_key).getAddress(prim_key)
   
    file = address.split(',')[0]
    byte = int(address.split(',')[1])
    f = open(file,"r+")
    f.seek(byte-1)
    f.write("0")
    page_start = byte - (byte % PAGESIZE)
    f.seek(page_start)
    f.write("0")

    btr = bTrees[type_name].delete(prim_key)

    return True

def updateRecord(type_name, prim_key, fields):

    types = getAllTypeNames()

    if type_name not in types:
        return False
    
    b_tree = bTrees[type_name]
    
    leftMost = b_tree.leftmost_leaf()
    keys = []

    while leftMost is not None:
        keys.extend(leftMost.keys) 
        leftMost =  leftMost.next 
    
    if prim_key not in keys:
        return False

    address = bTrees[type_name].find(prim_key).getAddress(prim_key)

    updfields =""
    for fd in fields:
        a = '{:20}'.format(fd)
        updfields = updfields + a
    
    file = address.split(',')[0]
    byte = int(address.split(',')[1])
    f = open(file,"r+")
    f.seek(byte)
    f.write(updfields)
    
    


    return True

def searchRecord(type_name, prim_key):

    types = getAllTypeNames()

    if type_name not in types:
        return None,False
    
    b_tree = bTrees[type_name]
    
    leftMost = b_tree.leftmost_leaf()
    keys = []

    while leftMost is not None:
        keys.extend(leftMost.keys) 
        leftMost =  leftMost.next 
    
    if prim_key not in keys:
        return None,False

    systemCat = open("systemCatalog.csv")

    lines = systemCat.readlines()

    text = ""

    for line in lines:
        if line[0: len(type_name)] == type_name:
            text = line
            break

    nofFields = int(text.split(",")[1])
    
    address = bTrees[type_name].find(prim_key).getAddress(prim_key)
    #print("address search ",address)
    file = address.split(',')[0]
    byte = int(address.split(',')[1])
    f = open(file,"r")
    f.seek(byte)
    #print("nof fields", nofFields)
    fields = f.read(20*nofFields).split()
    tofile = " ".join(fields)
    return tofile, True
 

def listRecord(type_name, outputFile):

    types = getAllTypeNames()

    if type_name not in types:
        return False

    b_tree = bTrees[type_name]
    
    leftMost = b_tree.leftmost_leaf()
    keys = []

    while leftMost is not None:
        keys.extend(leftMost.keys) 
        leftMost =  leftMost.next   

    keys.sort

    if len(keys)==0:
        return False 
    
    for key in keys:
        result,success = searchRecord(type_name,key)
        outputFile.write(result+"\n")
    
    

    return True

def filterRecord(type_name, condition, outputFile):

    types = getAllTypeNames()

    if type_name not in types:
        return False
    
    


    b_tree = bTrees[type_name]
    
    leftMost = b_tree.leftmost_leaf()
    keys = []

    while leftMost is not None:
        keys.extend(leftMost.keys) 
        leftMost =  leftMost.next   

    i = 0
    for key in keys:
        if key.isnumeric():
            keys[i] = int(key)
        i = i+1

    keys.sort()
    systemCat = open("systemCatalog.csv")

    lines = systemCat.readlines()

    text = ""

    for line in lines:
        if line[0: len(type_name)] == type_name:
            text = line
            break

    pkey_order = int(text.split(",")[2])

    b = text.split(",")[3+(pkey_order-1)*2].strip("][")
    b2 = b.replace("'","") 
    pkey_name = b2.replace(" ","")    
    

    if ">" in condition:
        a = condition.split(">")
        no = -1
        edge = ""
        if a[0] == pkey_name:
            no= 1
            edge = a[1].strip()
        elif a[1]  == pkey_name:
            edge = a[0].strip()
            no = 0
        else: 
            return False
        result=""

        for key in keys:

            if str(key).isnumeric():
                key = int(key)
                edge = int(edge)
            if no == 0 and key < edge:  # 5>id
                result,success = searchRecord(type_name,str(key))
                outputFile.write(result+"\n")
                
            if no ==1 and key > edge:   #id > 5
                result,success = searchRecord(type_name,str(key))
                outputFile.write(result+"\n")
        
    if "<" in condition:
        #id<3
        a = condition.split("<")
        no = -1
        edge = ""
        if a[0] == pkey_name:
            no= 1
            edge = a[1].strip()
        elif a[1] == pkey_name:
            edge = a[0].strip()
            no = 0
        else: 
            return False
        result=""

        for key in keys:

            if str(key).isnumeric():
                key = int(key)
                edge = int(edge)
            if no == 0 and key > edge:  # 5<id
                result,success = searchRecord(type_name,str(key))
                outputFile.write(result+"\n")
                
            if no ==1 and key < edge:   #id < 5
                result,success = searchRecord(type_name,str(key))
                outputFile.write(result+"\n")

    if "=" in condition:
        a = condition.split("=")
       
        edge = ""
        if a[0] == pkey_name:
            
            edge = a[1].strip()
        elif a[1]  == pkey_name:
            edge = a[0].strip()
        
        else:
            return False
            
        result=""

        for key in keys:

            if str(key).isnumeric():
                key = int(key)
                edge = int(edge)
            if  key == edge:  # 5=id
                result,success = searchRecord(type_name,str(key))
                outputFile.write(result+"\n")
                
            
        
            



    return True

def saveBTrees():

    
    type_names = getAllTypeNames()
    i = 0
    #print(type_names,"savebtreesdeki typenames")
  
    #print(len(bTrees))
    #print(len(type_names))
    for bTree_name in bTrees:
        leaves = []
        values = []
        dic = {}
        bTree = bTrees[bTree_name]
        file = open("bTree"+type_names[i]+".txt", "w+")

        leftMost = bTree.leftmost_leaf()


        while leftMost is not None:
            leaves.extend(leftMost.keys)
            values.extend(leftMost.values) 
            leftMost =  leftMost.next      

        for j in range(len(leaves)):
            dic[leaves[j]] = values[j]

        file.write(str(json.dumps(dic)))

        i = i + 1

        file.close()


def getAllTypeNames():
    systemCat = open("systemCatalog.csv", "r+")

    types = systemCat.readlines()
    type_names = []

    for type in types:
        type_names.append(type.split(',')[0])

    return type_names

def createbTrees():

    type_names = getAllTypeNames()

    i = 0

    for type_name in type_names:

        file = open("bTree"+type_names[i]+".txt", "r+")

        bplustree = BPlusTree()

        text = file.read()
        #print(text)

        dic = json.loads(text)

        for key in dic:
            bplustree.insert(key, dic[key])

        bTrees[type_name] = bplustree

        i = i + 1



if __name__ == '__main__':
    #demo()

    createbTrees()

    #print(len(bTrees))

    inputFileName = sys.argv[1]
    outputFileName = sys.argv[2]


    inputFile = open(inputFileName, 'r')
    outputFile = open(outputFileName, 'w')
    logFile = open('horadrimLog.csv','a+')

    lines = inputFile.readlines()

    for line in lines:
        #print(line)
        words = line.split()

        if len(words) == 0:
            continue


        if words[0].lower() == "create" and words[1].lower() == "type":
            type_name = words[2]
            nof_fields = int(words[3])
            prim_key_order = int(words[4])

            prim_key = words[3+2*prim_key_order]

            fieldsAndTypes = [None] * nof_fields*2

            for i in range(nof_fields*2):
                fieldsAndTypes[i] = words[5+i]

            success = createType(type_name, nof_fields, prim_key_order, fieldsAndTypes)


        if words[0].lower() == "delete" and words[1].lower() == "type":
            type_name = words[2]

            success = deleteType(type_name)

        if words[0].lower() == "list" and words[1].lower() == "type":

            success = listType(outputFile)

        if words[0].lower() == "create" and words[1].lower() == "record":
            type_name = words[2]
            fields = []

            for i in range(3,len(words)):
                fields.append(words[i])

            success = createRecord(type_name, fields)

        if words[0].lower() == "delete" and words[1].lower() == "record":
            type_name = words[2]
            prim_key = words[3]

            success = deleteRecord(type_name, prim_key)

        if words[0].lower() == "update" and words[1].lower() == "record":
            type_name = words[2]
            prim_key = words[3]
            fields = []

            for i in range(4,len(words)):
                fields.append(words[i])

            success = updateRecord(type_name, prim_key, fields)

        if words[0].lower() == "search" and words[1].lower() == "record":
            type_name = words[2]
            prim_key = words[3]

            result,success = searchRecord(type_name, prim_key)

            if result is not None:
                outputFile.write(result+"\n")

            


        if words[0].lower() == "list" and words[1].lower() == "record":
            type_name = words[2]

            success = listRecord(type_name, outputFile)

        if words[0].lower() == "filter" and words[1].lower() == "record":
            type_name = words[2]
            condition = words[3]

            success = filterRecord(type_name, condition, outputFile)


        if success:
            x = "success"
        else:
            x = "failure"

        logFile.write(str(int(time.time())) + "," + line.strip() + "," + x+"\n")

    
  
    """bplustree = BPlusTree()
    random_list = random.sample(range(1, 100), 20)
    random_list = ["a", "b", "c"]
    for i in random_list:
        bplustree[i] = 'test' + str(i)
        print('Insert ' + str(i))
        bplustree.show()

    bTrees["Angel"] = bplustree"""

    #print(bTrees['Angel'].find("5").keys)

    saveBTrees()
    #print(checkFileEmpty("berf_1.txt"))
    outputFile.close()
    inputFile.close()



