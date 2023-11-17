include "BPTNode.dfy"

class BPTree {
    var root: BPTNode?

    // ghost set for verifivation
    ghost var LeavesList: seq<BPTNode> 
    ghost var Contents: set<int> 
    ghost var Repr: set<object> // maybe change to object, for now I think I will just have nodes in it, not this (Tree)

    constructor Init()
        ensures Valid() 
        ensures fresh(Repr - {this})
        ensures Contents == {}
    { 
        root := null;
        Repr := {}; // TODO maybe we should add this in Repr
        Contents := {};
    } 


// COMMENT: currently not using this, just experimenting if verification is easier with more or less helper functions
    method SplitLeaf(current:BPTNode, val:int) returns(newNode:BPTNode)
        modifies current, current.children, current.keys
        requires current.Valid()
        requires !(val in current.Contents)
        // ensures newNode.Valid()
        // ensures current.Valid()
        // ensures current.keyNum > 0
        // ensures current.keys[current.keyNum-1] < newNode.keys[0]
        // ensures old(current.Content) < (current.Content + newNode.Content)
        // ensures val in (current.Content + newNode.Content)
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
        // pointers rearrangement -> adding this causes timeout when verifying 
    //    newNode.nextLeaf := current.nextLeaf;
    //    current.nextLeaf := newNode;

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
        
        current.Contents := {};
        for i := 0 to current.keyNum {
            current.Contents := current.Contents + {current.keys[i]};
        }
        for i := 0 to newNode.keyNum {
            newNode.Contents := newNode.Contents + {newNode.keys[i]};
        }
    }

    
    // this is at least 3rd version of insert, but having constant trouble with iterating through arrays and modifying them and showing that they keep the sorted properties, often getting timeout
/*   
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
*/

/*
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
            assert node.Valid(); 
            if node.keyNum < ORDER { // there is place for new key in the leaf
                node.InsertAtLeaf(x);
                newNode := node;
                assert newNode.Valid();
            } else { // not enough space in the leaf, splitting the leaf
                // TODO be careful here with Content and Repr, you have to move them as well
            //    assert node.Valid();
                var splitNode := new BPTNode.Init();
                var temp := new int[ORDER + 1]; // storing all keys and the new value in temporary list
                for i := 0 to ORDER + 1 
                    modifies temp
                { // Initialization 
                    temp[i] := 0;
                }

                /*    var i := 0; // fining right position for new value
                while x > temp[i] && i < ORDER {
                    i := i + 1;
                } */
                
                assert node.Valid();
                var i := node.GetInsertIndex(x);
                assert 0 <= i <= node.keyNum;

                for j := 0 to i 
                    invariant 0 <= j <= i 
                    modifies temp
                { // copy all keys from the leaf (the leaf is full)
                    temp[j] := node.keys[j];
                }
                temp[i] := x;
                for j := i + 1 to ORDER + 1 
                    invariant 0 < j <= ORDER + 1
                    modifies temp
                {
                    temp[j] := node.keys[j - 1];
                }

                // start of rearrangement 
                node.keyNum := (ORDER + 1) / 2; // +1 just defines if there will be more keys in first or second node in case of odd number of keys
                splitNode.keyNum := (ORDER + 1) - (ORDER + 1) / 2;

                splitNode.nextLeaf := node.nextLeaf;
                node.nextLeaf := splitNode;

                // pointers rearrangement --> this is OLD version (in which we used children array instead of the nextLeaf variable)
            //    assert node.keyNum < ORDER;
            //    assert splitNode.keyNum < ORDER;
            //    assert node.children.Length == ORDER;
            //    node.children[node.keyNum] := splitNode;
            //    splitNode.children[splitNode.keyNum] := node.children[ORDER];
            //    node.children[ORDER] := null;

                node.Contents := {};
                var keyNum := node.keyNum;
                for i := 0 to keyNum 
                    modifies node, node.keys // node added here because of updating Contents
                    invariant 0 <= i <= keyNum < ORDER
                    invariant keyNum == node.keyNum
                { 
                    node.keys[i] := temp[i];
                    node.Contents := node.Contents + {temp[i]}; 
                }
                for i := node.keyNum to ORDER 
                    modifies node.keys
                    invariant 0 <= i <= ORDER
                    invariant node.keys in node.Repr
                {
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
        
        } /* else {
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
        } */

    }
*/
    
    // COMMENT
    // not optimized version of Find, checks all children, not just the child in which the value should be
    method Find(val: int) returns (inTree: bool)
        requires Valid()
        ensures root == null ==> inTree == false
        ensures root != null ==> (root.ContainsVal(val) <==> inTree)
        ensures Valid()
    {
        if root == null { return false; }
        else { inTree := FindHelper(root, val); }
    }
    
    static method FindHelper(node: BPTNode, val: int) returns (inTree: bool) // verifies correct in under 100 seconds
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

// COMMENT:
// This is regular version of Find where you search only in the appropriate leaf (using sorted property), 
// but even with many tried out options for verification, we could not get this to work, probably because it seems that
// the connection between keys and Contents is not clear to Dafny (and also that everything important is before index keyNum), even with our predicates
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

    
    ghost predicate LeavesValid()
        reads this, Repr, LeavesList
        requires root != null
    {
        // all leaves are in ghost var
        (forall leaf :: (leaf in Repr) && (leaf is BPTNode) && leaf.isLeaf ==> leaf in LeavesList)&&
        // all leaves are pointing towards the next 
        (forall j :int :: 0 <= j < |LeavesList|-1 ==> LeavesList[j].nextLeaf ==  LeavesList[j+1]) &&
        // all keys in Content are in the Leaves List contents
        (forall key :: key in Contents ==>  key in root.SumOfChildContents(LeavesList))
    }    

    ghost predicate Valid()
    reads * // TODO see if possible to reduce
    {
        (root == null ==> Contents == {}) && 
        (root != null ==> 
            root in Repr && root.Repr <= Repr && // TODO maybe root.Repr == Repr (depends if we put this in Repr)
            root.Valid() &&
            Contents == root.Contents &&
            root is BPTNode &&
            (!root.isLeaf ==> 
                forall i : int :: 0<= i < root.keyNum ==> root.children[i].HalfFull())&&
            LeavesValid()
        )
    }

}