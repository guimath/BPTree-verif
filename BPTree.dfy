include "BPTNode.dfy"
// include "Utils.dfy"

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
        Repr := {this}; // TODO maybe we should add this in Repr
        Contents := {};
    } 

    // OVERALL COMMENT: most of the functions are commented because we often get timeout. Do check comment line before each function


    // COMMENT: newNode and current both independantly can verify the first three ensures (if you comment other part)
    // but if I add them both verification times out (tried with no limit, no result after ~10min) 
    static method SplitLeaf(current:BPTNode, val:int) returns(newNode:BPTNode)
        modifies current, current.Repr
        requires current.Valid()
        requires !(val in current.Contents)
        requires val > 0
        requires current.isLeaf
        requires current.keyNum == ORDER
        ensures current.Valid()  && newNode.Valid()
        ensures current.isLeaf    && newNode.isLeaf
        ensures current.HalfFull() && newNode.HalfFull()
        ensures current.keyNum > 0 && newNode.keyNum > 0
        ensures current.keys[current.keyNum-1] < newNode.keys[0]
        ensures fresh(newNode)
        // these ensures do not verify
        ensures old(current.Contents) < (current.Contents + newNode.Contents)
        ensures val in (current.Contents + newNode.Contents)
        ensures current.Contents !! newNode.Contents
        ensures forall k :: k in newNode.Contents ==> (newNode.keys[0] <= k)
        ensures forall k :: k in current.Contents ==> (k < newNode.keys[0])
    { 
/*
        newNode := new BPTNode.Init();
        var temp := new int[ORDER + 1]; // storing all keys and the new value in temporary list
        var idx := current.GetInsertIndex(val);
        for i := 0 to idx 
            modifies temp
            invariant 0<= i <= idx
            invariant forall j: int :: 0 <= j < i ==> (
                temp[j] == current.keys[j]
            )
            {temp[i] := current.keys[i];}

        for i := idx +1 to ORDER+1 
            modifies temp
            invariant idx+1<= i <= ORDER+1 
            invariant forall j: int :: 0 <= j < idx ==> (
                temp[j] == current.keys[j]
            )
            // invariant forall j: int :: 0 <= j < current.keyNum ==> (
            //     current.keys[j] > 0
            // )
            invariant forall j: int :: idx < j < i ==> (
                temp[j] == current.keys[j-1]
            )
            {temp[i] := current.keys[i-1];}

        temp[idx] := val;
        assert 0 < idx ==> temp[idx-1] < temp[idx] ;
        assert idx < current.keyNum ==> temp[idx] < temp[idx+1];
        assert (forall i,j :: 0<= i< j < current.keyNum+1 ==> (
            temp[i] < temp[j]
        ));
        assert temp[0] > 0;
        assert forall j: int :: 0 <= j < ORDER+1 ==> (
                temp[j] > 0
        );

        current.keyNum := (ORDER + 1) / 2;
        newNode.keyNum := (ORDER + 1) - (ORDER + 1) / 2;
        // // pointers rearrangement -> adding this causes timeout when verifying 
        newNode.nextLeaf := current.nextLeaf;
        current.nextLeaf := newNode;

        // ************* current ************* // 
        // TODO OPTIMIZE 
        for i := 0 to current.keyNum  
            modifies current.keys
            invariant 0 <= i <= current.keyNum
            invariant forall j: int :: 0 <= j < i ==> (
                current.keys[j] == temp[j]
            )
            {current.keys[i] := temp[i];}

        assert forall j: int :: 0 <= j < current.keyNum ==> (
            current.keys[j] == temp[j]
        );

        // COMMENT: next assert added for the ensures
        // assert forall k: int :: k in current.keys[..current.keyNum] ==> (
        //     k < temp[current.keyNum]
        // );

        for i := current.keyNum to ORDER 
            modifies current.keys
            invariant current.keyNum <= i <= ORDER
            invariant forall j: int :: current.keyNum <= j < i ==> (
                current.keys[j] == 0
            )
            invariant forall j: int :: 0 <= j < current.keyNum ==> (
                current.keys[j] == temp[j]
            )
            {current.keys[i] := 0;}
                
        current.Repr := {current} + {current.children} + {current.keys};
        assert current.KeysInRepr();
        assert current.ValidBeforeContentUpdate();
        current.AddKeysContent();
        assert current.Valid(); // independantly verified
        assert current.isLeaf; 
        assert current.keyNum > 0; 

        // ************* newNode ************* //
        var offset := current.keyNum;
        for i := 0 to newNode.keyNum 
            modifies newNode.keys
            invariant 0 <= i <= newNode.keyNum
            invariant forall j: int :: 0 <= j < i ==> (
                newNode.keys[j] == temp[offset+j]
            )
            {newNode.keys[i] := temp[offset+i];}
        
        for i := newNode.keyNum to ORDER 
            modifies newNode.keys
            invariant newNode.keyNum <= i <= ORDER
            invariant forall j: int :: newNode.keyNum <= j < i ==> (
                newNode.keys[j] == 0
            )
            invariant forall j: int :: 0 <= j < newNode.keyNum ==> (
                newNode.keys[j] == temp[offset+j]
            )
            {newNode.keys[i] := 0;}

        newNode.Repr := {newNode} + {newNode.children} + {newNode.keys};
        assert newNode.KeysInRepr();
        assert newNode.ValidBeforeContentUpdate();
        newNode.AddKeysContent();
        assert newNode.Valid();// independantly verified
        assert newNode.isLeaf; 
        assert newNode.keyNum > 0;

        assert forall k :: k in newNode.keys[..newNode.keyNum] ==> (newNode.keys[0] <= k);
        assert forall k :: k in current.keys[..current.keyNum] ==> (k < newNode.keys[0]);
        
        // COMMENT: unable to verify next 2 assert ==> again problems with understanding equalities betweeen set and sequence
        // COMMENT: when I changed keysInContents to be more similar, timeout after 300 seconds
        // assert forall k :: k in newNode.keys[..newNode.keyNum] <==> k in newNode.Contents;
        // assert forall k :: k in current.keys[..current.keyNum] <==> k in current.Contents;
    */
    }

    // COMMENT: splitNode does not work currently
    // // adds newnode to current node 


    static method SplitNode(current:BPTNode, child:BPTNode) returns(newNode:BPTNode)
        modifies current, current.Repr
        requires current.Valid()
        requires child.Valid()
        requires !(child.keys[0] in current.Contents)
        requires !current.isLeaf
        ensures fresh(newNode)
        ensures !current.isLeaf && !newNode.isLeaf
        ensures current.Valid() && newNode.Valid()
        ensures child.Valid()
        ensures old(child.Contents) == child.Contents // same 
        ensures current.HalfFull() && newNode.HalfFull()
        ensures current.keyNum > 0 && newNode.keyNum > 0
        ensures current.keys[current.keyNum-1] < newNode.keys[0]
        ensures old(current.Contents) < (current.Contents + newNode.Contents) // all values kept
        ensures current.Contents !! newNode.Contents // disjoint
        ensures old(current.Contents)+child.Contents == current.Contents + newNode.Contents // all values kept
    {
        newNode := new BPTNode.Init();
        var newInternal: BPTNode := new BPTNode.Init();
        var tempKey := new int[ORDER + 1];
        var tempChildren := new BPTNode?[ORDER + 2];

        for i := 0 to ORDER {
            tempKey[i] := current.keys[i];
            tempChildren[i] := current.children[i];
        }
        tempChildren[ORDER] := current.children[ORDER];

        var i := 0;
        while child.keys[0] > tempKey[i] && i < ORDER { // in the internal node we want to insert first key of the newly created node (==newNode)
            i := i + 1; // finding the right position
        }

        for j := ORDER + 1 downto i {
            tempKey[j] := tempKey[j - 1]; 
        }
        tempKey[i] := child.keys[0]; // inserted key in its position
        for j := ORDER + 2 downto i {
            tempChildren[j] := tempChildren[j - 1];
        }
        tempChildren[i + 1] := newNode; // same for the pointers - new pointer in correct position

        newInternal.isLeaf := false;
        current.keyNum := (ORDER + 1) / 2; // splitting the keys
        newInternal.keyNum := ORDER - (ORDER + 1) / 2;

        current.Contents := {};
        current.Repr := {current} + {current.children} + {current.keys}; // starting fresh
        for i := 0 to current.keyNum {
            current.keys[i] := tempKey[i];
            current.Contents := current.Contents + {tempKey[i]}; 
            current.children[i] := tempChildren[i];
            current.Repr := current.Repr + current.children[i].Repr;
        }
        current.children[current.keyNum] := tempChildren[current.keyNum];
        for i := current.keyNum to ORDER - 1 {
            current.keys[i] := 0; 
        }

        var j := current.keyNum;
        for i := 0 to newInternal.keyNum {
            newInternal.keys[i] := tempKey[j];
            newInternal.Contents := newInternal.Contents + {tempKey[j]};
            j := j + 1;
        }
        j := current.keyNum + 1;
        for i := 0 to newInternal.keyNum + 1 {
            newInternal.children[i] := tempChildren[j];
            newInternal.Repr := newInternal.Repr + newInternal.children[i].Repr;
            j := j + 1; 
        }
        
    }  
  

    // // COMMENT: not even sure if we successfully verified this or got timeout
    static method InsertInNode(node:BPTNode, newNode:BPTNode) 
        requires node.Valid()
        requires newNode.Valid()
        requires node.NotFull() 
        requires !(newNode in node.Repr)
        requires !node.ContainsVal(newNode.keys[0])
        modifies node, node.keys, node.children
        ensures node.Valid()
        ensures (newNode in node.Repr)
    {
        /*
        var idx := node.GetInsertIndex(newNode.keys[0]);
        if idx < node.keyNum {
            for j := node.keyNum-1 downto idx
                modifies node.keys
                invariant 0<= idx <= j <=   node.keyNum - 1
            {
                node.keys[j+1] := node.keys[j];
            }

            assert idx <= node.keyNum ==> (idx + 1 <= node.keyNum + 1);
            for j := node.keyNum downto idx 
                modifies node.children
                invariant 0<= idx <= j <=   node.keyNum
            {
                node.children[j+1] := node.children[j];
            }
        }

        node.keys[idx] := newNode.keys[0];
        node.Contents := node.Contents + newNode.Contents;
        node.keyNum := node.keyNum + 1;
        node.children[idx + 1] := newNode;
        node.Repr := node.Repr + newNode.Repr;
        */
    }

    

    // COMMENT: this is who knows which version of insert, but having constant trouble with iterating through arrays and modifying them and showing that they keep the sorted properties, often getting timeout
    
    method Insert(val: int)
        requires Valid()
        modifies Repr
        ensures Valid()
        ensures val > 0 ==> Contents == old(Contents) + {val}
        ensures val <= 0 ==> Contents == old(Contents)
    {
        // edge case 1 : negative val  
        if val <= 0 {
            assert Valid();
            return;// TODO return error 
        }
        // edge case 2 : val already in tree *
        var valInTree := Find(val);
        if valInTree{
            assert Valid();
            assert Contents == old(Contents) + {val};
            return;
        }
        assert val !in Contents;
        // edge case 3 if root is null == first key in the tree ever
        if root == null { 
            // creating root (as leaf) and adding key
            root := new BPTNode.Init();
            root.keys[0] := val;
            root.keyNum := 1;
            root.Contents := {root.keys[0]};
            Contents := root.Contents;
            Repr := root.Repr + {this};
            assert Valid();
            assert Contents == old(Contents) + {val};
            return;
            // postcond satisfied
        }
        else { // root is BPTNode && val > 0
            var updateParent : bool;
            assert this !in root.Repr;
            root, updateParent := InsertHelper(root, false, val);
            assert updateParent == false;
            assert val in root.Contents;
            assert root.Valid();
            Contents := root.Contents;
            Repr := root.Repr + {this};
            return;
        }
    }


    static method CreateNewParent(firstChild:BPTNode, secondChild:BPTNode) returns (newParent:BPTNode) 
        requires firstChild.Valid() && !firstChild.Empty()
        requires secondChild.Valid() && !secondChild.Empty()
        requires firstChild.height == secondChild.height
        requires forall k :: k in firstChild.Contents ==> (k < secondChild.keys[0])
        requires forall k :: k in secondChild.Contents ==> (secondChild.keys[0] <= k)
        ensures newParent.Valid()
        ensures forall k :: k in firstChild.Contents ==> k in newParent.Contents
        ensures forall k :: k in secondChild.Contents ==> k in newParent.Contents
        ensures firstChild.Valid()
        ensures secondChild.Valid()
        // ensures newParent.Contents == firstChild.Contents + secondChild.Contents
        ensures fresh(newParent)
    {
        newParent := new BPTNode.Init();
        newParent.keyNum := 1;
        newParent.keys[0] := secondChild.keys[0];
        newParent.children[0] := firstChild;
        newParent.children[1] := secondChild;
        newParent.isLeaf := false;
        newParent.height := firstChild.height +1;
        newParent.Contents := firstChild.Contents + secondChild.Contents;
        newParent.Repr := newParent.Repr + firstChild.Repr + secondChild.Repr; 
        assert old(firstChild) == firstChild;
        assert old(secondChild) == secondChild;
        return;  
    }


    // COMMENT: every part verifying with verif error: "This postcondition might not hold: node.ContainsVal(x) || newNode.ContainsVal(x)" (but no red lines, this caused because not all paths shown)
    // COMMENT: but whole function causes timeout in 100 seconds (I think this was before adding the createNewParent, and with this first part alone verifies faster, but together seems not)
    // new node is either new Root or a new node
    static method InsertHelper(node:BPTNode, hasParent:bool, x:int) returns (newNode:BPTNode, updateParent:bool)
        requires node.Valid()
        requires x !in node.Contents
        requires x > 0
        modifies node, node.Repr
        ensures newNode.Valid() 
        ensures node.Valid()
        ensures node.ContainsVal(x) || newNode.ContainsVal(x)
        ensures newNode == node || fresh(newNode)
        ensures hasParent == false ==> updateParent == false
        ensures old(node.Contents) + {x} == node.Contents + newNode.Contents
        ensures hasParent == false ==> newNode.Contents == old(node.Contents) + {x}                                                         // if it does not have parent, it is the root node, so return value must be the new root, so it def has new value in the Contents 
        decreases  node.height
    {
        newNode := new BPTNode.Init();
        updateParent := false;
        // // node is leaf == no more recursion
        if node.isLeaf {
            assert node.Valid(); 
            // node.keyNum < ORDER == there is place for new key in the leaf
            if node.keyNum < ORDER {
                //inserting in the leaf (no additional node required)
                node.InsertAtLeaf(x);
                newNode := node;
                updateParent := false;

                assert newNode.Valid();
                assert node.Valid();
                assert node.ContainsVal(x) || newNode.ContainsVal(x);
                assert newNode == node; 
                assert newNode == node ==> (newNode == node || fresh(newNode));
                assert newNode == node || fresh(newNode);

                return;
            } 

            // not enough space in the leaf ==> splitting the leaf
            var splitNode: BPTNode := SplitLeaf(node, x);
            assert node.ContainsVal(x) || splitNode.ContainsVal(x);
            // hasParent==false <==> node was root  
            if !hasParent {
                // creates new root at height +1
                newNode := CreateNewParent(node, splitNode);
                updateParent  := false; 

                assert newNode.Valid();
                assert node.Valid();
                // assert node.ContainsVal(x) || newNode.ContainsVal(x);
                // assert newNode == node || fresh(newNode);

                return;  
            }  
            // if not, we need to update parent node
            updateParent := true;
            newNode := splitNode;
            return;
        } 

        // // node is not leaf 
        // if !node.isLeaf {
        assert node.isLeaf == false;
        var innerUpdateParent := false;
        var innerNewNode : BPTNode;

        // COMMENT: recursive call prolongs the verification (but next two lines and everything before verifies in less than 70 seconds)
        var idx := GetInsertIndex(node.keys, node.keyNum, x); // node.GetInsertIndex(x);
        innerNewNode, innerUpdateParent := InsertHelper(node.children[idx], true, x);
        // // if innerUpdateParent && node.keyNum == ORDER {
        // if !innerUpdateParent {
        //     node.Contents := {};
        //     node.Repr := {node} + {node.children} + {node.keys};
        //     for i:= 0 to node.keyNum+1 {
        //         node.Contents := node.Contents + node.children[i].Contents;
        //         node.Repr := node.Repr + node.children[i].Repr;
        //     }
        //     newNode := node;
        //     updateParent := false;
        //     return;
        // }
        
        // if node.keyNum < ORDER {
        //     InsertInNode(node, innerNewNode);
        //     newNode := node; // TODO check that is note erasing 
        //     updateParent := false;
        //     return; 
        // } 
        // newNode := SplitNode(node, newNode);
        // updateParent := true;
        // return;
        // }
    }



    // COMMENT : Whole find function verifies
    method Find(val: int) returns (inTree: bool)
        requires Valid()
        ensures root == null ==> inTree == false
        ensures root != null ==> (root.ContainsVal(val) <==> inTree)
        ensures Valid()
    {
        if root == null { return false; }
        else { inTree := FindHelper(root, val); }
    }
     

    // COMMENT: verified successfully now
    method FindHelper(node: BPTNode, val: int) returns (inTree: bool) // verifies correct in under 100 seconds
        requires node.Valid()
        ensures node.ContainsVal(val) <==> inTree
        decreases node.Repr
    {        
        if node.keyNum == 0 {
            assert !node.ContainsVal(val); // Having this assert as well as the second one results in timeout
            return false;
        }
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
            assert !node.ContainsVal(val); // Having this assert as well as the second one results in timeout
            return false;
        }
        if node.keyNum > 0 && !node.isLeaf {
            var idx := node.keyNum;
            for i := 0 to node.keyNum 
                invariant 0 <= i <= node.keyNum 
                invariant 0 < i ==> node.keys[i-1] < val
            {
                if val == node.keys[i]  {
                    assert node.ContainsVal(val); // Having this assert as well as the second one results in timeout
                    return true; // verifies assert node.ContainsVal(val);
                }
                if val < node.keys[i] {
                    idx := i;
                    assert idx == i;
                    assert 0 < idx ==> node.keys[idx-1] < val;
                    break;
                }
            }   
            assert idx < node.keyNum ==> val < node.keys[idx];
            assert 0< idx ==> node.keys[idx-1] < val;
            assert node.Hierarchy();
            
            assert forall i: int :: 0 <= i < node.keyNum ==>
                (forall k :: k in node.children[i].Contents ==> 
                    k < node.keys[i]);
            assert 1<= idx < node.keyNum+1 ==> 
                (forall k :: k in node.children[idx-1].Contents ==> 
                        k < node.keys[idx-1]);
            assert 1<= idx < node.keyNum+1 ==> 
                (forall k :: k in node.children[idx-1].Contents ==> 
                        k < val);       
            assert 1 <= idx < node.keyNum+1 ==> !node.children[idx-1].ContainsVal(val);
            assert forall j :: 0< j < idx ==> !node.children[j].ContainsVal(val);
            

            assert forall j :: idx < j < node.keyNum+1 ==> !node.children[j].ContainsVal(val);

            assert forall j :: 0 < j < node.keyNum+1 ==> j != idx ==> !node.children[j].ContainsVal(val);

            inTree := FindHelper(node.children[idx], val);
            // assert 0< idx ==> !node.children[idx-1].ContainsVal(val);
            assert node.ContainsVal(val) <==> inTree; //This assert doesn't complete
            return inTree; // Why success ?
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


    // TODO I was trying to reproduce our example where this !in root.Repr solved the problem with verifying newRoot.Valid(), but I could not reproduce it
    method experiment()
        modifies this, Repr
    {
        root := new BPTNode.Init();
        Repr := root.Repr + {this};
        Contents := root.Contents;
        
        assert root.Valid(); 
        // assert Valid();
        // assert this !in root.Repr;

        var newNode : BPTNode? := new BPTNode.Init();
        assert root.Valid();
        newNode := root;
        assert newNode.Valid();

        root := null;
        // assert this !in newNode.Repr;
        assert newNode.Valid();

    }

    ghost predicate HalfKeys()
        reads this, root, Repr
        requires root is BPTNode
        requires root in Repr && root.Repr <= Repr
        requires root.Valid() 
    {
        (!root.isLeaf ==> 
            forall i : int :: 0<= i < root.keyNum ==> root.children[i].HalfFull())
    }

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
 // TODO see if possible to reduce
 // TODO maybe root.Repr == Repr (depends if we put this in Repr)
    ghost predicate Valid()
    reads *
    {   
        this in Repr &&
        (root == null ==> Contents == {}) && 
        (root != null ==> 
            root in Repr && root.Repr <= Repr && 
            !(this in root.Repr) && 
            root.Valid() &&
            Contents == root.Contents &&
            root is BPTNode &&
            HalfKeys()
            // LeavesValid()
        )
    }
}


ghost predicate SortedSeq(a: seq<int>)
  //sequence is sorted from left to right
{
  (forall i,j :: 0<= i< j < |a| ==> ( a[i] < a[j] ))
}

method GetInsertIndex(a: array<int>, limit: int, x:int) returns (idx:int)
  // get index so that array stays sorted
  requires x !in a[..]
  requires 0 <= limit <= a.Length
  requires SortedSeq(a[..limit])
  ensures 0<= idx <= limit
  ensures SortedSeq(a[..limit])
  ensures idx > 0 ==> a[idx-1]< x
  ensures idx < limit ==> x < a[idx]
{
  idx := limit;
  for i := 0 to limit
    invariant i>0 ==> x > a[i-1]
  {
    if x < a[i] {
      idx := i;
      break;
    }
  }
}
