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
        requires root.height > -1
        ensures current.isLeaf
    {
        current := root;
        parent := null;
        assert current.Valid();
        assert current.height > -1;
        
        while (current.height > -1) 
            decreases current.height
            invariant current.Valid()
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
            assert idx <= parent.keyNum < ORDER +1;
            current := parent.children[idx];
            assert current is BPTNode;
            assert parent.height > -1; 
            assert current.height == parent.height-1;
        }
        assert current.isLeaf;
    }

/*
    method Insert1(val: int) // TODO: add ptrs from one leaf to another
        requires Valid()
        //requires root==null ==> fresh(root)
        modifies this, Repr, root
        ensures Valid()
        ensures Contents == old(Contents) + {val}
    {
        //TODO add check that value is not already in tree
        if root == null { // if there was no root, root becomes leaf node with only this inserted value in it
            root := new BPTNode.Init();
            root.keys[0] := val;
            root.keyNum := 1;
            root.Contents := {root.keys[0]};
            Repr := Repr + root.Repr;
            assert root.keyNum == 1;
            assert root.Contents == {root.keys[0]}; // TODO not sure if necessary 
        } else {
            assert root.height > -1;
            var current, parent := GetInsertLeaf(val);
            if current.keyNum < ORDER {
                current.InsertAtLeaf(val);
            }
            else {
                var newNode := new BPTNode.Init();
                var temp := new int[ORDER + 1]; // storing all keys and the new value in temporary list
                var idx := current.GetInsertIndex(val);
                for i := 0 to idx { // copy all keys from the leaf (the leaf is full)
                    temp[i] := current.keys[i];
                }
                for i := idx +1 to ORDER+1 { // copy all keys from the leaf (the leaf is full)
                    temp[i] := current.keys[i-1];
                }
                temp[idx] := val;
                // TODO ASSERT SORTED

                current.keyNum := (ORDER + 1) / 2;
                newNode.keyNum := (ORDER + 1) - (ORDER + 1) / 2;
                // TODO pointers rearrangement

                // updating values
                for i := 0 to current.keyNum - 1 { 
                    current.keys[i] := temp[i];
                    current.Contents := current.Contents + {temp[i]}; 
                }
                for i := current.keyNum to ORDER - 1 {
                    current.keys[i] := 0;
                }
                for i := 0 to newNode.keyNum - 1{
                    current.keys[i] := temp[current.keyNum+i];
                    newNode.Contents := newNode.Contents + {temp[current.keyNum+i]}; 
                }
                if current == root { // if current was root than we just create a new root with one key
                    var newRoot := new BPTNode.Init();
                    newRoot.keyNum := 1;
                    newRoot.keys[0] := newNode.keys[0];
                    newRoot.children[0] := current;
                    newRoot.children[1] := newNode;
                    newRoot.isLeaf := false;
                    newRoot.height := newRoot.height+1;
                    newRoot.Contents := newRoot.Contents + current.Contents + newNode.Contents;
                    newRoot.Repr := newRoot.Repr + current.Repr + newNode.Repr; 
                    root := newRoot;
                }
                else  {
                    ShiftLevel(newNode.keys[0], parent, newNode);
                }
            }
        }
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
            var i := 0;
            while i < node.keyNum 
                invariant 0 <= i <= node.keyNum
                invariant 1 <= i <= node.keyNum ==> ( val > node.keys[i - 1] )  
                invariant forall j : int :: 0 <= j < i <= node.keyNum ==> (!ValInSubTree(node.children[j], val))
            {
                if val <= node.keys[i] {
                    inTree := FindHelper(node.children[i], val);
                    assert ( ValInSubTree(node.children[i], val) ==> inTree == true );
                    assert ( !ValInSubTree(node.children[i], val) ==> inTree == false );
                    assert node.Valid() ==> node.children[i].Contents <= node.Contents;
                    assert node.Hierarchy() ==> (i > 0 && val < node.keys[i] ==> ( node.keys[i - 1] <= val ));

                //    assert ( node.Hierarchy() && node.keys[i - 1] <= val < node.keys[i] && !ValInSubTree(node.children[i], val) ) ==> !ValInSubTree(node, val);
                    return;
                } 
                i := i + 1;
            }

            assert val > node.keys[node.keyNum - 1];
            assert forall i : int :: 0 <= i < node.keyNum ==> (!ValInSubTree(node.children[i], val));
            inTree := FindHelper(node.children[node.keyNum], val);
            assert ( ValInSubTree(node.children[node.keyNum], val) ==> inTree == true );
            assert ( !ValInSubTree(node.children[node.keyNum], val) ==> inTree == false );
            
        //    assert node.isLeaf == false ==> (node.Valid() ==> (node.Contents == node.SumOfChildContents(node.children[0..node.keyNum+1]))); // TIMEOUT
        //    assert (val in node.children[node.keyNum].Contents ==> val in node.Contents);
        //    assert val in node.Contents ==> ValInSubTree(node, val);
            assert ValInSubTree(node.children[node.keyNum], val) ==> ValInSubTree(node, val);
            assert node.Contents == node.SumOfChildContents(node.children[0..node.keyNum+1]);
        /*    assert !ValInSubTree(node.children[node.keyNum], val) ==> !ValInSubTree(node, val) by {
                assert forall i : int :: 0 <= i < node.keyNum ==> (!ValInSubTree(node.children[i], val));
                assert node.Contents == node.SumOfChildContents(node.children[0..node.keyNum+1]);
            }
            assert ValInSubTree(node.children[node.keyNum], val) == ValInSubTree(node, val) by {
                assert forall i : int :: 0 <= i < node.keyNum ==> (!ValInSubTree(node.children[i], val));
                assert ValInSubTree(node.children[node.keyNum], val) ==> ValInSubTree(node, val);
                assert !ValInSubTree(node.children[node.keyNum], val) ==> !ValInSubTree(node, val);
            } */
        //    assert ( ValInSubTree(node, val) ==> val in node.children[node.keyNum].Contents); // DOES NOT HOLD
        //    assert (exists i: int :: 0 <= i <= node.keyNum && val in node.children[i].Contents) ==> inTree == true; // TIMEOUT
            assert ( ValInSubTree(node, val) ==> inTree == true );
            assert ( !ValInSubTree(node, val) ==> inTree == false );
   //         assert ( (forall i: int :: 0 <= i <= node.keyNum ==> ( !ValInSubTree(node.children[i], val))) ==> inTree == false);
            return;
        }

    } 

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