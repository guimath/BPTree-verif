include "BPTNode.dfy"

class BPTree {
    var root: BPTNode?

    // ghost set for verifivation
    ghost var Contents: set<int> 
    ghost var Repr: set<object> // maybe change to object, for now I think I will just have nodes in it, not this (Tree)

    constructor Init()
        ensures Valid() 
        ensures fresh(Repr - {this})
        ensures Contents == {}
    { 
        root := null;
        Repr := {};
        Contents := {};
    } 

    method GetInsertLeaf(val:int) returns (current:BPTNode, parent:BPTNode?)
        requires Valid()
        requires root is BPTNode
        requires root.Valid()
        ensures current.isLeaf
        ensures current.Valid()
        ensures current in Repr
        ensures current.keys in Repr
        ensures parent is BPTNode ==> parent.Valid()
    {
        current := root;
        parent := null;
        while (current.height > -1) 
            decreases current.height
            invariant current.Valid()
            invariant parent is BPTNode ==> parent.Valid()
        {
            parent := current;
            var idx := parent.keyNum;
            assume parent.keyNum>ORDER/2; // TODO lower value for keynum in BPTnode
            for i := 0 to parent.keyNum  {
                if val < parent.keys[i] { 
                    idx := i;
                    break;
                }
            }
            current := parent.children[idx];
        }

        assume current in Repr;
        assume current.keys in Repr;
    }

    method BackProp(node: BPTNode, val:int)
        requires node.Valid()
        ensures Contents == old(Contents) + {val}
        ensures Valid()
    {
        assume Contents == old(Contents) + {val};
        assume Valid();
    }

    method SplitNode(current:BPTNode, val:int) returns(newNode:BPTNode)
        modifies current, current.children, current.keys
        requires current.Valid()
        requires !(val in current.Contents)
        ensures newNode.Valid()
        ensures current.Valid()
        ensures current.keyNum > 0
        ensures current.keys[current.keyNum-1] < newNode.keys[0]
    {
        newNode := new BPTNode.Init();
        var temp := new int[ORDER + 1]; // storing all keys and the new value in temporary list
        var idx := current.GetInsertIndex(val);
        for i := 0 to idx 
            modifies temp
            invariant forall j: int :: 0 <= j < i ==> (
                temp[j] == current.keys[j]
            )
            {temp[i] := current.keys[i];}

        for i := idx +1 to ORDER+1 
            modifies temp
            invariant forall j: int :: 0 <= j < idx ==> (
                temp[j] == current.keys[j]
            )
            invariant forall j: int :: idx < j < i ==> (
                temp[j] == current.keys[j-1]
            )
            {temp[i] := current.keys[i-1];}

        temp[idx] := val;
        assert 0 < idx ==> temp[idx-1] < temp[idx] ;
        assert idx < current.keyNum ==> temp[idx] < temp[idx+1];
        // TODO patch ASSERT temp SORTED
        // assume forall j: int :: 0 <= j < ORDER ==> (temp[j] < temp[j+1]);

        current.keyNum := (ORDER + 1) / 2;
        newNode.keyNum := (ORDER + 1) - (ORDER + 1) / 2;
        // TODO pointers rearrangement

        for i := 0 to current.keyNum - 1 
            modifies current.keys
            {current.keys[i] := temp[i];}

        for i := current.keyNum to ORDER - 1 
            modifies current.keys
            {current.keys[i] := 0;}
        
        var offset := current.keyNum - 1;
        for i := 0 to newNode.keyNum - 1 
            modifies newNode.keys
            {newNode.keys[i] := temp[offset+i];}
    }

    method ShiftLevel(val: int, current: BPTNode, child: BPTNode) 
    // val is value to be inserted, current is the node in which we are trying to insert and child is newly created leaf node
        requires Valid()
        requires current.Valid()
        modifies this, current, Repr
        ensures Valid()
        // decreases if root == null then {} else root.Repr - current.Repr
    {
        return;
    }
    
    method Insert(val: int)
        requires Valid()
        modifies Repr    
        ensures Valid()
        ensures Contents == old(Contents) + {val}
    {
        var updateParent := false;
        root, updateParent := InsertHelper(null, root, val);
        assert updateParent == false;
        assert root.Valid();
        Contents := root.Contents;
        Repr := root.Repr + {this}; // completely updating the Repr, not using old one
    }

    static method InsertHelper(parent:BPTNode?, node:BPTNode?, x:int) returns (newNode:BPTNode, updateParent:bool)
        requires (node!=null && parent!=null) ==> (node in parent.Repr&& parent.height == node.height+1 && parent !in node.Repr)
        requires node == null || (node.Valid())
        requires node == null ==> parent == null
        requires node != null ==> x !in node.Contents // TODO remove this and use Find -> if it is already in tree, don't do anything
        requires parent!=null ==> parent.Valid()
        requires parent!=null ==> parent.isLeaf==false
        modifies if node!= null then node.Repr else {}
        modifies parent
    //    ensures newNode.Valid()
    //    ensures parent == null ==> updateParent == false
    //    ensures parent !=null ==> (parent.Contents == old(parent.Contents+{x}))
    //    ensures node !=null ==> node.Valid()
    //    ensures node == old(node)
    //    ensures parent == old(parent)
    //    decreases if node == null then {} else node.Repr 
    {
        newNode := new BPTNode.Init();
        updateParent := false;

        if node == null { // first key in the tree ever (root was null)
            assert parent == null;
            newNode.keys[0] := x;
            newNode.keyNum := 1;
            newNode.Contents := {newNode.keys[0]};
            assert newNode.keyNum == 1;
            assert newNode.Contents == {newNode.keys[0]}; 
            assert newNode.Valid();
            
        } else if node.isLeaf == true { 
            if node.keyNum < ORDER { // there is place for new key in the leaf
                node.InsertAtLeaf(x);
                newNode := node;
                assert newNode.Valid();
            } else { // not enough space in the leaf, splitting the leaf
                // TODO be careful here with Content and Repr, you have to move them as well
                var splitNode := new BPTNode.Init();
                var temp := new int[ORDER + 1]; // storing all keys and the new value in temporary list
                for i := 0 to ORDER + 1 { // Initialization 
                    temp[i] := 0;
                }

                /*    var i := 0; // fining right position for new value
                while x > temp[i] && i < ORDER {
                    i := i + 1;
                } */
                assert node.Valid();
                var i := node.GetInsertIndex(x);
                assert 0 <= i < node.keyNum;

                for j := 0 to i 
                    invariant 0 <= j < i 
                { // copy all keys from the leaf (the leaf is full)
                    temp[j] := node.keys[j];
                }
                temp[i] := x;
                for j := i + 1 to ORDER + 1 {
                    temp[j] := node.keys[j - 1];
                }

                // start of rearrangement 
                node.keyNum := (ORDER + 1) / 2;
                splitNode.keyNum := (ORDER + 1) - (ORDER + 1) / 2;

                // pointers rearrangement - TODO maybe using special variable for leaf pointers
                node.children[node.keyNum] := newNode;
                splitNode.children[newNode.keyNum] := splitNode.children[ORDER];
                node.children[ORDER] := null;

                node.Contents := {};
                for i := 0 to node.keyNum { 
                    node.keys[i] := temp[i];
                    node.Contents := node.Contents + {temp[i]}; 
                }
                for i := node.keyNum to ORDER {
                   node.keys[i] := 0;
                }

                var j := node.keyNum;
                for i := 0 to newNode.keyNum {
                    splitNode.keys[i] := temp[j];
                    splitNode.Contents := splitNode.Contents + {temp[j]}; 
                    j := j + 1;
                }
            
                assert node.isLeaf == true && splitNode.isLeaf == true;

                if parent == null { // if node was root than we just create a new root with one key
                    var newRoot := new BPTNode.Init();
                    newRoot.keyNum := 1;
                    newRoot.keys[0] := splitNode.keys[0];
                    newRoot.children[0] := node;
                    newRoot.children[1] := splitNode;
                    newRoot.isLeaf := false;
                    newRoot.Contents := node.Contents + splitNode.Contents;
                    newRoot.Repr := newRoot.Repr + node.Repr + splitNode.Repr; 
                    
                    newNode := newRoot;
                } else { // if not, we need to update parent node
                    updateParent := true;
                    newNode := splitNode;
                }
            }
        
        } else {
            assert node.isLeaf == false && node.Valid();
            var updateNode := false;
            var i := 0;
            while i < node.keyNum { // find a child in which we want to insert and call recursion
                if x < node.keys[i] { // TODO be careful with < and <= signs
                    newNode, updateNode := InsertHelper(node, node.children[i], x); // newNode is children[i]
                    break;
                }

                if i == node.keyNum - 1 { // if the value is greater than all possible go to last child
                    newNode, updateNode := InsertHelper(node, node.children[i + 1], x);
                    break;
                }
                i := i + 1;
            }

            // if we need to update current node (meaning its child got splitted)
            if updateNode {
                if node.keyNum < ORDER { // enough space in current internal node => we just add new key
                    var i := 0;
                    // value that we want to insert now is the first key in newly created node (== newNode)
                    while i < node.keyNum && newNode.keys[0] > node.keys[i] 
                        invariant 0 <= i <= node.keyNum
                    {
                        i := i + 1; // find right position
                    }
            
                    for j := node.keyNum - 1 downto i {
                        node.keys[j] := node.keys[j - 1];
                    }

                    assert i <= node.keyNum ==> (i + 1 <= node.keyNum + 1);
                    for j := node.keyNum downto i + 1 {
                        node.children[j] := node.children[j - 1];
                    }
                    node.keys[i] := newNode.keys[0];
                    node.Contents := node.Contents + {newNode.keys[0]};
                    node.keyNum := node.keyNum + 1;
                    node.children[i + 1] := newNode;
                    node.Repr := node.Repr + newNode.Repr;
                    
                } else { // internal node should also be splitted
                    var newInternal: BPTNode := new BPTNode.Init();
                    var tempKey := new int[ORDER + 1];
                    var tempChildren := new BPTNode?[ORDER + 2];

                    for i := 0 to ORDER {
                        tempKey[i] := node.keys[i];
                        tempChildren[i] := node.children[i];
                    }
                    tempChildren[ORDER] := node.children[ORDER];

                    var i := 0;
                    while newNode.keys[0] > tempKey[i] && i < ORDER { // in the internal node we want to insert first key of the newly created node (==newNode)
                        i := i + 1; // finding the right position
                    }

                    for j := ORDER + 1 downto i {
                        tempKey[j] := tempKey[j - 1]; 
                    }
                    tempKey[i] := x; // inserted key in its position
                    for j := ORDER + 2 downto i {
                        tempChildren[j] := tempChildren[j - 1];
                    }
                    tempChildren[i + 1] := newNode; // same for the pointers - new pointer in correct position

                    newInternal.isLeaf := false;
                    node.keyNum := (ORDER + 1) / 2; // splitting the keys
                    newInternal.keyNum := ORDER - (ORDER + 1) / 2;

                    node.Contents := {};
                    node.Repr := {node} + {node.children} + {node.keys}; // starting fresh
                    for i := 0 to node.keyNum {
                        node.keys[i] := tempKey[i];
                        node.Contents := node.Contents + {tempKey[i]}; 
                        node.children[i] := tempChildren[i];
                        node.Repr := node.Repr + node.children[i].Repr;
                    }
                    node.children[node.keyNum] := tempChildren[node.keyNum];
                    for i := node.keyNum to ORDER - 1 {
                        node.keys[i] := 0; 
                    }

                    var j := node.keyNum;
                    for i := 0 to newInternal.keyNum {
                        newInternal.keys[i] := tempKey[j];
                        newInternal.Contents := newInternal.Contents + {tempKey[j]};
                        j := j + 1;
                    }
                    j := node.keyNum + 1;
                    for i := 0 to newInternal.keyNum + 1 {
                        newInternal.children[i] := tempChildren[j];
                        newInternal.Repr := newInternal.Repr + newInternal.children[i].Repr;
                        j := j + 1;
                    }

                    if parent == null { // again, if parent does not exist (this was the root) 
                        var newRoot := new BPTNode.Init();
                        newRoot.keys[0] := newInternal.keys[0];
                        newRoot.children[0] := node;
                        newRoot.children[1] := newInternal;
                        newRoot.isLeaf := false;
                        newRoot.keyNum := 1;
                        newRoot.Contents := newRoot.Contents + node.Contents + newNode.Contents;
                        newRoot.Repr := newRoot.Repr + node.Repr + newNode.Repr; 

                        newNode := newRoot;
                    } else {
                        updateParent := true;
                        newNode := newInternal;
                    }
                }
            } else {
                node.Contents := {};
                node.Repr := {node} + {node.keys} + {node.children};
                for i := 0 to node.keyNum + 1 {
                    node.Contents := node.Contents + node.children[i].Contents;
                    node.Repr := node.Repr + node.children[i].Repr;
                }
            } 
        } 

    }
    
  /*  
    method Insert1(val: int) // TODO: add ptrs from one leaf to another
        requires Valid()
        requires val != 0
        //requires root==null ==> fresh(root)
        modifies this, Repr, root
        ensures Valid()
        ensures Contents == old(Contents) + {val}
    {
        var f := Find(val);
        if f {return;} // TODO return error code ?
        if root == null { // if there was no root, root becomes leaf node with only this inserted value in it
            root := new BPTNode.Init();
            root.keys[0] := val;
            root.keyNum := 1;
            root.Contents := {root.keys[0]};
            Contents := root.Contents;
            Repr := Repr + root.Repr;
            return;
        }

        var current, parent := GetInsertLeaf(val);
        assume current.Contents <= root.Contents; //TODO PATCH
        assert !(val in current.Contents);
        if current.keyNum < ORDER {
            current.InsertAtLeaf(val);
            BackProp(current, val);
            return;
        }
        assume current in Repr;
        assume current.keys in Repr;
        assume current.children in Repr;
        var newNode := SplitNode(current, val);
        if current == root { // if current was root than we just create a new root with one key
            var newRoot := new BPTNode.Init();
            newRoot.keyNum := 1;
            newRoot.keys[0] := newNode.keys[0];
            newRoot.children[0] := current;
            newRoot.children[1] := newNode;
            newRoot.isLeaf := false;
            newRoot.height := newNode.height+1;
            newRoot.Contents := newRoot.Contents + current.Contents + newNode.Contents;
            newRoot.Repr := newRoot.Repr + current.Repr + newNode.Repr; 
            root := newRoot;
            return;
        }
        ShiftLevel(newNode.keys[0], parent, newNode);
    }
    */

/*
    method Insert(val: int) // TODO: add ptrs from one leaf to another
        requires Valid()
        modifies this, Repr
        ensures Valid()
        ensures Contents == old(Contents) + {val}
    {
        if root == null { // if there was no root, root becomes leaf node with only this inserted value in it
            root := new BPTNode.Init();
            root.keys[0] := val;
            root.keyNum := 1;
            assert root.keyNum == 1 <==> root.Contents == {root.keys[0]}; // TODO not sure if necessary 
            assert root.Valid(); // TODO probably remove this from here
        } else {
            assert root != null;
            var current := root;
            var parent: BPTNode?;

            assert current != null;

            // reach the leaf in which we should insert value
            while !current.isLeaf 
                decreases current.Repr {
                parent := current;

                var i := 0;
                while i < current.keyNum {
                    if val < current.keys[i] { // TODO be careful with < and <= signs
                        current := current.children[i];
                        break;
                    }

                    if i == current.keyNum - 1 { // if the value is greater than all possible go to last child
                        current := current.children[i + 1];
                        break;
                    }
                    i := i + 1;
                }
            }

            assert current.Valid(); // TODO do we need this?
            assert current.isLeaf == true;
            
            // now we have reached leaf in which we are inserting the value 
            if current.keyNum < ORDER { // the node in which we are inserting is not full
                var i := 0;
                while i < current.keyNum && val < current.keys[i] {
                    i := i + 1; // find location where the value should be inserted
                }

                for j: int := current.keyNum downto i {
                    current.keys[j] := current.keys[j - 1]; // adjust other elements
                }
                current.keys[i] := val;

                current.keyNum := current.keyNum + 1; // increase number of keys in the leaf

                current.children[current.keyNum] := current.children[current.keyNum - 1]; // adjust pointer to next leaf
                current.children[current.keyNum - 1] := null;

                current.Contents := current.Contents + {val}; // TODO all parents etc need to get Contents updated, maybe add while iterating or sth?
            }
            // not enough space in the leaf (splitting required)
            else {  // TODO be careful here with Content and Repr, you have to move them as well
                var newNode := new BPTNode.Init();
                var temp := new int[ORDER + 1]; // storing all keys and the new value in temporary list
                for i := 0 to ORDER { // Initialization 
                    temp[i] := 0;
                }

                for i := 0 to ORDER { // copy all keys from the leaf (the leaf is full)
                    temp[i] := current.keys[i];
                }

                var i := 0; // fining right position for new value
                while val > temp[i] && i < ORDER {
                    i := i + 1;
                }

                for j := ORDER downto i {
                    temp[j] := temp[j - 1];
                }
                temp[i] := val;

                // start of rearrangement 
                current.keyNum := (ORDER + 1) / 2;
                newNode.keyNum := (ORDER + 1) - (ORDER + 1) / 2;

                // pointers rearrangement
                current.children[current.keyNum] := newNode;
                newNode.children[newNode.keyNum] := current.children[ORDER];
                current.children[ORDER] := null;

                current.Contents := {};
                for i := 0 to current.keyNum - 1 { 
                   current.keys[i] := temp[i];
                    current.Contents := current.Contents + {temp[i]}; 
                }
                for i := current.keyNum to ORDER - 1 {
                   current.keys[i] := 0;
                }

                var j := current.keyNum;
                for i := 0 to newNode.keyNum - 1 {
                    newNode.keys[i] := temp[j];
                    newNode.Contents := newNode.Contents + {temp[j]}; 
                    j := j + 1;
                }
            
                assert current.isLeaf == true && newNode.isLeaf == true;

                if current == root { // if current was root than we just create a new root with one key
                    var newRoot := new BPTNode.Init();
                    newRoot.keyNum := 1;
                    newRoot.keys[0] := newNode.keys[0];
                    newRoot.children[0] := current;
                    newRoot.children[1] := newNode;
                    newRoot.isLeaf := false;
                    newRoot.Contents := newRoot.Contents + current.Contents + newNode.Contents;
                    newRoot.Repr := newRoot.Repr + current.Repr + newNode.Repr; 
                    root := newRoot;
                } else { // if not, we need to update parent node
                    ShiftLevel(newNode.keys[0], parent, newNode);
                }
            }

        }

        Contents := root.Contents;
        Repr := root.Repr ;
    } */

/*
    method ShiftLevel(val: int, current: BPTNode, child: BPTNode) 
    // val is value to be inserted, current is the node in which we are trying to insert and child is newly created leaf node
        requires Valid()
        requires current.Valid()
        modifies this, current, Repr
        ensures Valid()
        decreases if root == null then {} else root.Repr - current.Repr
    {
        if current.keyNum < ORDER { // if new key can fit into parent node (parent is not full)
            var i := 0;
            while i < current.keyNum && val > current.keys[i] 
                invariant 0 <= i <= current.keyNum
            {
                i := i + 1; // find right position
            }
            
            for j := current.keyNum downto i {
                current.keys[j] := current.keys[j - 1];
            }

            assert i <= current.keyNum ==> (i + 1 <= current.keyNum + 1);
            for j := current.keyNum + 1 downto i + 1 {
                current.children[j] := current.children[j - 1];
            }
            current.keys[i] := val;
            current.keyNum := current.keyNum + 1;
            current.children[i + 1] := child;
            current.Contents := current.Contents + {val}; // TODO this should be propagated upwards 
            current.Repr := current.Repr + child.Repr;
        } else { // internal node should also be splitted
            var newInternal: BPTNode := new BPTNode.Init();
            var tempKey := new int[ORDER + 1];
            var tempChildren := new BPTNode?[ORDER + 2];

            for i := 0 to ORDER {
                tempKey[i] := current.keys[i];
                tempChildren[i] := current.children[i];
            }
            tempChildren[ORDER] := current.children[ORDER];

            var i := 0;
            while val > tempKey[i] && i < ORDER {
                i := i + 1; // finding the right position
            }

            for j := ORDER + 1 downto i {
                tempKey[j] := tempKey[j - 1]; 
            }
            tempKey[i] := val; // inserted key in its position
            for j := ORDER + 2 downto i {
                tempChildren[j] := tempChildren[j - 1];
            }
            tempChildren[i + 1] := child; // same for the pointers - new pointer in correct position

            newInternal.isLeaf := false;
            current.keyNum := (ORDER + 1) / 2; // splitting the keys
            newInternal.keyNum := ORDER - (ORDER + 1) / 2;


            // TODO -> update vrijednosti u current
            current.Contents := {};
            for i := 0 to current.keyNum - 1 {
                current.keys[i] := tempKey[i];
                current.Contents := current.Contents + {tempKey[i]}; 
            }
            for i := current.keyNum to ORDER - 1 {
                current.keys[i] := 0; 
            }

            var j := current.keyNum;
            for i := 0 to newInternal.keyNum {
                newInternal.keys[i] := tempKey[j];
                j := j + 1;
            }
            j := current.keyNum + 1;
            for i := 0 to newInternal.keyNum + 1 {
                newInternal.children[i] := tempChildren[j];
                j := j + 1;
            }

            if current == root { // again, if previous is 
                var newRoot := new BPTNode.Init();
                newRoot.keys[0] := newInternal.keys[0];
                newRoot.children[0] := current;
                newRoot.children[1] := newInternal;
                newRoot.isLeaf := false;
                newRoot.keyNum := 1;
                root := newRoot;
            } else {
                var parent := FindParent(root, current);
                ShiftLevel(current.keys[current.keyNum], parent, newInternal);
            }
        }
    } 
*/
    

    method FindParent(current: BPTNode, child: BPTNode) returns (parent: BPTNode?) 
        requires Valid()
        requires current.Valid()
        ensures Valid()
        decreases current.height
    /* {
        if current.isLeaf || current.children[0].isLeaf {
            return null;
        }

        for i := 0 to current.keyNum + 1 {
            if current.children[i] == child {
                parent := current;
                return parent;
            } else {
                assert current.Valid() ==> current.children[i].Valid();
                parent := FindParent(current.children[i], child);
                if parent != null {
                    return parent;
                }
            }
        }
        return null;
    } */
    {
        if current.isLeaf || current.children[0].isLeaf {
            return null;
        }

        parent := null; // Initialize parent to null

        var i := 0;
        while i <= current.keyNum && parent == null 
            decreases current.keyNum - i // Ensure a decreasing loop variant
        {
            if current.children[i] == child {
                parent := current;
                return parent;
            } else {
                i := i + 1;
            }
        }
    
        if parent == null {
            // If we haven't found the parent yet, continue searching in child nodes
            i := 0;
            while i <= current.keyNum && parent == null
                decreases current.keyNum - i // Ensure a decreasing loop variant
            {
                assert current.children[i].Valid();
                parent := FindParent(current.children[i], child);
                i := i + 1;
            }
        }
    
        return parent;
    }
    
    
    // GUILHEM's version
    method Find(val: int) returns (inTree: bool)
        requires Valid()
        ensures root == null ==> inTree == false
        ensures root != null ==> (root.ContainsVal(val) <==> inTree)
        ensures Valid()
    {
        if root == null { return false; }
        else { inTree := FindHelper(root, val); }
    }
    
    static method FindHelper(node: BPTNode, val: int) returns (inTree: bool)
        requires node.Valid()
        ensures node.ContainsVal(val) <==> inTree
        decreases node.Repr
    {        
        if node.keyNum == 0 {return false;}
        if node.isLeaf == true {
            var keyNum := node.keyNum;
            var i := 0;
            while i< keyNum
                invariant forall j: int :: 0 <= j < i<= keyNum ==> node.keys[j] != val
                invariant 0 <= i <= keyNum
            {
                if node.keys[i] == val {return true;}
                i := i+1;
            }
            return false;
        }
        ghost var IgnContents : set<int> := {};
        var i := 0;
        while i < node.keyNum+1 
            invariant 0 <= i <= node.keyNum+1 
            invariant forall j : int :: 0 <= j < i ==> (!node.children[j].ContainsVal(val))
            invariant !(val in IgnContents)
        {
            if node.children[i] is BPTNode {
                var tmp := FindHelper(node.children[i], val);
                if tmp {return true;} 
                IgnContents := IgnContents + node.children[i].Contents;
            }
            i := i+1;
        }
        return false;
    }
    // assert forall j : int :: 0 <= j < node.keyNum+1 ==> (!ValInSubTree(node.children[j], val));
    // assert !(val in IgnContents); 
    // // assert IgnContents == node.SumOfChildContents(node.children[0..node.keyNum+1]);
    // // assert IgnContents >= node.Cokntents;
    // assert (!ValInSubTree(node, val));



   /* 
    method Find(val: int) returns (inTree: bool)
        requires Valid()
        ensures root == null ==> inTree == false
        ensures root != null ==> ( ValInSubTree(this.root, val) ==> inTree == true )
        ensures root != null ==> ( !ValInSubTree(this.root, val) ==> inTree == false ) 
        ensures Valid()
    {
        if root == null { return false; }
        else { inTree := FindHelper(root, val); }
    }
    

    static method FindHelper(node: BPTNode, val: int) returns (inTree: bool)
        requires node.Valid()
        ensures node.Empty() ==> inTree == false
        ensures ( !node.Empty() && ValInSubTree(node, val) ) ==> inTree == true
        ensures ( !node.Empty() && !ValInSubTree(node, val) ) ==> inTree == false  
        decreases node.Repr
    {        
        if node.keyNum == 0 { 
            return false; }
        if node.isLeaf == true {
            assert |node.Contents| == node.keyNum;
            assert node.keyNum >= 1;
            inTree := false;
            var keyNum := node.keyNum;


            var i := 0;
            while i< keyNum
                invariant forall j: int :: 0 <= j < i<= keyNum ==> node.keys[j] != val
                invariant 0 <= i <= keyNum
            {
                if node.keys[i] == val {
                    inTree := inTree || true;
                //    assert ( node.keys[i] == val && node.KeysInContents() ) ==> val in node.Contents; // causes timeout
                    assert ValInSubTree(node, val) == true; // && inTree == true;
                    return;
                }
                i := i+1;
            }
            assert i == keyNum;
    //        assert inTree == false;
    //        assert node.keys[node.keyNum - 1] != val;
    //        assert val !in node.keys[..node.keyNum];
            assert forall i: int :: 0 <= i <= keyNum - 1 ==> ( node.keys[i] != val );
    //        assert val !in node.Contents; 
    //        assert ValInSubTree(node, val) == false;
            inTree := false;
            return;
        } else { 
            ghost var currentContents: set<int> := {};
         /*   assert ValInSubTree(node, val) ==> (exists i:int :: 0 <= i <= node.keyNum && (ValInSubTree(node.children[i], val))) by {
                assert ValInSubTree(node, val) ==> val in node.Contents;
                assert node.ChildrenContentsDisjoint() && node.Contents == node.SumOfChildrenContents(0, node.keyNum+1);
                assert (val in node.Contents ==> val in node.SumOfChildrenContents(0, node.keyNum+1)) ==> (exists i:int :: 0 <= i <= node.keyNum && val in node.children[i].Contents);
            } */
            var i := 0;
            assert val !in currentContents;
        //    assert currentContents == node.SumOfChildrenContents(0, i);
            while i < node.keyNum 
                invariant 0 <= i <= node.keyNum
                invariant 1 <= i <= node.keyNum ==> ( val > node.keys[i - 1] )  
                invariant forall j : int :: 0 <= j < i <= node.keyNum ==> (!ValInSubTree(node.children[j], val))
                invariant val !in currentContents
         //       invariant 1 <= i <= node.keyNum ==> (val !in node.SumOfChildrenContents(0, i - 1)) // TIMEOUT
                invariant i > 0 ==> currentContents == node.SumOfChildrenContents(0, i + 1) 
            {
            //    assert currentContents == node.SumOfChildrenContents(0, i);
                if val <= node.keys[i] {
                    inTree := FindHelper(node.children[i], val);
                    assert ( ValInSubTree(node.children[i], val) ==> inTree == true );
                    assert ( !ValInSubTree(node.children[i], val) ==> inTree == false );
                    assert node.Valid() ==> node.children[i].Contents <= node.Contents;
                    assert node.Hierarchy() ==> (i > 0 && val < node.keys[i] ==> ( node.keys[i - 1] <= val ));
                    assert val in node.children[i].Contents ==> val in node.Contents;
                    assert ValInSubTree(node.children[i], val) ==> ValInSubTree(node, val);
                //    assert forall j:int :: i < j <= node.keyNum ==> (forall x:int :: x in node.children[j].Contents ==> val < x);
                   
                //    assert ( node.Hierarchy() && node.keys[i - 1] <= val < node.keys[i] && !ValInSubTree(node.children[i], val) ) ==> !ValInSubTree(node, val);
                    return;
                } 
                i := i + 1;
                assert val !in node.children[i].Contents by { // without by MAY NOT HOLD    
                    assert val > node.keys[i];
                    assert forall x:int :: x in node.children[i].Contents ==> val > x;
                }
                currentContents := currentContents + node.children[i].Contents;
                assert currentContents == node.SumOfChildrenContents(0, i + 1);
            }

            assert val > node.keys[node.keyNum - 1];
            assert forall i : int :: 0 <= i < node.keyNum ==> (!ValInSubTree(node.children[i], val));
            assert val !in currentContents;
        //    assert (forall i : int :: 0 <= i < node.keyNum ==> (val !in node.children[i].Contents)) ==> (val !in node.SumOfChildrenContents(0, node.keyNum)); // MAY NOT HOLD (part after last ==>)
        //    assert val !in node.SumOfChildrenContents(0, node.keyNum); // TIMEOUT
            inTree := FindHelper(node.children[node.keyNum], val);
            assert ( ValInSubTree(node.children[node.keyNum], val) ==> inTree == true );
            assert ( !ValInSubTree(node.children[node.keyNum], val) ==> inTree == false );
            assert ValInSubTree(node.children[node.keyNum], val) ==> ValInSubTree(node, val);
        //    assert currentContents == node.SumOfChildrenContents(0, node.keyNum+1);
            currentContents := currentContents + node.children[node.keyNum].Contents;
        //    assert currentContents == node.SumOfChildrenContents(0, node.keyNum+2);
        
        //    assert currentContents == node.SumOfChildrenContents(0, node.keyNum+1);
            assert node.Contents == node.SumOfChildrenContents(0, node.keyNum+1);
        //    assert currentContents == node.Contents by {
        //        assert currentContents == node.SumOfChildrenContents(0, node.keyNum+1);
        //        assert node.Contents == node.SumOfChildrenContents(0, node.keyNum+1);
        //    }   
            
        //    assert node.isLeaf == false ==> (node.Valid() ==> (node.Contents == node.SumOfChildContents(node.children[0..node.keyNum+1]))); // TIMEOUT
        //    assert (val in node.children[node.keyNum].Contents ==> val in node.Contents);
        //    assert val in node.Contents ==> ValInSubTree(node, val);
        /*    assert ValInSubTree(node.children[node.keyNum], val) ==> ValInSubTree(node, val) by {
                assert forall i : int :: 0 <= i < node.keyNum ==> (!ValInSubTree(node.children[i], val));
                assert val !in node.SumOfChildrenContents(0, node.keyNum);
            } */
        /*    assert ValInSubTree(node.children[node.keyNum], val) ==> (ValInSubTree(node, val) && inTree == true) by {
                assert ( ValInSubTree(node.children[node.keyNum], val) ==> inTree == true );
                assert ValInSubTree(node.children[node.keyNum], val) ==> ValInSubTree(node, val);
            } */
            assert ValInSubTree(node.children[node.keyNum], val) ==> ValInSubTree(node, val) ==> inTree == true by {
                assert ( ValInSubTree(node.children[node.keyNum], val) ==> inTree == true );
                assert ValInSubTree(node.children[node.keyNum], val) ==> ValInSubTree(node, val);
            }
        //    assert forall i : int :: 0 <= i <= node.keyNum ==> (!ValInSubTree(node.children[i], val));
        //    assert node.Contents == node.SumOfChildrenContents(0, node.keyNum+1);
        //    assert node.Contents == currentContents;
            /*
            assert !ValInSubTree(node.children[node.keyNum], val) ==> !ValInSubTree(node, val) by {
                assert forall i : int :: 0 <= i <= node.keyNum ==> (!ValInSubTree(node.children[i], val));
            //    assert node.Contents == node.SumOfChildContents(node.children[0..node.keyNum+1]);
                assert val !in node.SumOfChildContents(node.children[0..node.keyNum+1]);
                assert val !in node.Contents;
            }
            
            assert ValInSubTree(node.children[node.keyNum], val) == ValInSubTree(node, val) by {
                assert forall i : int :: 0 <= i < node.keyNum ==> (!ValInSubTree(node.children[i], val));
                assert ValInSubTree(node.children[node.keyNum], val) ==> ValInSubTree(node, val);
                assert !ValInSubTree(node.children[node.keyNum], val) ==> !ValInSubTree(node, val);
            } */
            /* assert ( ValInSubTree(node, val) ==> val in node.children[node.keyNum].Contents) by {
                assert forall i : int :: 0 <= i < node.keyNum ==> (!ValInSubTree(node.children[i], val));
                assert ValInSubTree(node, val) ==> val in node.Contents;
                assert node.Contents == node.SumOfChildContents(node.children[0..node.keyNum+1]);
                assert (node.Valid() && node.isLeaf == false) ==> node.ChildrenContentsDisjoint();
            } // DOES NOT HOLD, with by ==> timeout 
            */
        //    assert ValInSubTree(node, val) ==> (exists i:int :: 0 <= i <= node.keyNum && (ValInSubTree(node.children[i], val)));
        //    assert (exists i: int :: 0 <= i <= node.keyNum && val in node.children[i].Contents) ==> inTree == true; // TIMEOUT

        /*    assert ValInSubTree(node, val) == ValInSubTree(node.children[node.keyNum], val) by {
                assert forall i : int :: 0 <= i < node.keyNum ==> (!ValInSubTree(node.children[i], val));
                assert val !in node.SumOfChildrenContents(0, node.keyNum);
                assert node.Contents == node.SumOfChildrenContents(0, node.keyNum) + node.children[node.keyNum].Contents;
            } */

            assert ( ValInSubTree(node, val) ==> inTree == true ); 
            /*
            by {
                assert val in node.Contents;
                assert node.Contents == node.SumOfChildContents(node.children[0..node.keyNum+1]);
                assert exists i:int :: 0 <= i <= node.keyNum ==> (val in node.children[i].Contents);
                
            } */
            assert ( !ValInSubTree(node, val) ==> inTree == false );
        //    assert ( (forall i: int :: 0 <= i <= node.keyNum ==> ( !ValInSubTree(node.children[i], val))) ==> inTree == false);
            return;
        }

    } 
    */

    
 /*   method Main()
        modifies this, Repr
    {
        // Create a new BPTree instance
        var tree := new BPTree.Init();
    
        // Insert a value into the tree
        tree.Insert1(42);

        // Verify that the value is in the Contents
        assert 42 in tree.Contents;

        print("Test passed: Value 42 added to the root.");

    } */

    ghost static predicate ValInSubTree(node: BPTNode, val: int) 
        reads node
    {
        val in node.Contents
    }


    ghost predicate Valid()
    reads * // TODO see if possible to reduce
    {
        (root == null ==> Contents == {}) && 
        (root != null ==> 
            root in Repr && root.Repr <= Repr && // TODO maybe root.Repr == Repr (depends if we put this in Repr)
            root.Valid() &&
            Contents == root.Contents)
    } // TODO maybe add sth like it contains all values in leaf nodes (which you can iterate through using leaf pointers)

}