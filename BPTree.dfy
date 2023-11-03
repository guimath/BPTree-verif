include "BPTNode.dfy"

class BPTree {
    var root: BPTNode?

    // ghost set for verifivation
    ghost var Contents: set<int> 
    ghost var Repr: set<BPTNode> // maybe change to object, for now I think I will just have nodes in it, not this (Tree)

    constructor Init()
        ensures Well() 
 //       ensures fresh(Repr - {this})
        ensures Contents == {}
    { 
        root := null;
        Repr := {};
        Contents := {};
    } 

    method Insert(val: int) // TODO: add ptrs from one leaf to another
        requires Well()
        modifies this, Repr
        ensures Well()
        ensures Contents == old(Contents) + {val}
    {
        if root == null { // if there was no root, root becomes leaf node with only this inserted value in it
            root := new BPTNode.init();
            root.keys[0] := val;
            root.keynum := 1;
            assert root.keynum == 1 <==> root.Contents == {root.keys[0]}; // TODO not sure if necessary 
            assert root.well(); // TODO probably remove this from here
        } else {
            assert root != null;
            var current := root;
            var parent: BPTNode?;

            assert current != null;

            // reach the leaf in which we should insert value
            while !current.is_leaf 
                decreases current.Repr {
                parent := current;

                var i := 0;
                while i < current.keynum {
                    if val < current.keys[i] { // TODO be careful with < and <= signs
                        current := current.children[i];
                        break;
                    }

                    if i == current.keynum - 1 { // if the value is greater than all possible go to last child
                        current := current.children[i + 1];
                        break;
                    }
                    i := i + 1;
                }
            }

            assert current.well(); // TODO do we need this?
            assert current.is_leaf == true;
            
            // now we have reached leaf in which we are inserting the value 
            if current.keynum < ORDER { // the node in which we are inserting is not full
                var i := 0;
                while i < current.keynum && val < current.keys[i] {
                    i := i + 1; // find location where the value should be inserted
                }

                for j: int := current.keynum downto i {
                    current.keys[j] := current.keys[j - 1]; // adjust other elements
                }
                current.keys[i] := val;

                current.keynum := current.keynum + 1; // increase number of keys in the leaf

                current.children[current.keynum] := current.children[current.keynum - 1]; // adjust pointer to next leaf
                current.children[current.keynum - 1] := null;

                current.Contents := current.Contents + {val}; // TODO all parents etc need to get Contents updated, maybe add while iterating or sth?
            }
            // not enough space in the leaf (splitting required)
            else {  // TODO be careful here with Content and Repr, you have to move them as well
                var newNode := new BPTNode.init();
                var temp := new int[ORDER + 1]; // storing all keys and the new value in temporary list
                for i := 0 to ORDER { // initialization 
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
                current.keynum := (ORDER + 1) / 2;
                newNode.keynum := (ORDER + 1) - (ORDER + 1) / 2;

                // pointers rearrangement
                current.children[current.keynum] := newNode;
                newNode.children[newNode.keynum] := current.children[ORDER];
                current.children[ORDER] := null;

                current.Contents := {};
                for i := 0 to current.keynum - 1 { 
                    current.keys[i] := temp[i];
                    current.Contents := current.Contents + {temp[i]}; 
                }
                for i := current.keynum to ORDER - 1 {
                    current.keys[i] := 0;
                }

                var j := current.keynum;
                for i := 0 to newNode.keynum - 1 {
                    newNode.keys[i] := temp[j];
                    newNode.Contents := newNode.Contents + {temp[j]}; 
                    j := j + 1;
                }
            
                assert current.is_leaf == true && newNode.is_leaf == true;

                if current == root { // if current was root than we just create a new root with one key
                    var newRoot := new BPTNode.init();
                    newRoot.keynum := 1;
                    newRoot.keys[0] := newNode.keys[0];
                    newRoot.children[0] := current;
                    newRoot.children[1] := newNode;
                    newRoot.is_leaf := false;
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
    }

    method ShiftLevel(val: int, current: BPTNode, child: BPTNode) 
    // val is value to be inserted, current is the node in which we are trying to insert and child is newly created leaf node
        requires Well()
        requires current.length_ok()
        requires current.well()
        modifies this, current, Repr
        ensures Well()
        decreases if root == null then {} else root.Repr - current.Repr
    {
        if current.keynum < ORDER { // if new key can fit into parent node (parent is not full)
            var i := 0;
            while i < current.keynum && val > current.keys[i] 
                invariant 0 <= i <= current.keynum
            {
                i := i + 1; // find right position
            }
            
            for j := current.keynum downto i {
                current.keys[j] := current.keys[j - 1];
            }

            assert i <= current.keynum ==> (i + 1 <= current.keynum + 1);
            for j := current.keynum + 1 downto i + 1 {
                current.children[j] := current.children[j - 1];
            }
            current.keys[i] := val;
            current.keynum := current.keynum + 1;
            current.children[i + 1] := child;
            current.Contents := current.Contents + {val}; // TODO this should be propagated upwards 
            current.Repr := current.Repr + child.Repr;
        } else { // internal node should also be splitted
            var newInternal: BPTNode := new BPTNode.init();
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

            newInternal.is_leaf := false;
            current.keynum := (ORDER + 1) / 2; // splitting the keys
            newInternal.keynum := ORDER - (ORDER + 1) / 2;


            // TODO -> update vrijednosti u current
            current.Contents := {};
            for i := 0 to current.keynum - 1 {
                current.keys[i] := tempKey[i];
                current.Contents := current.Contents + {tempKey[i]}; 
            }
            for i := current.keynum to ORDER - 1 {
                current.keys[i] := 0; 
            }

            var j := current.keynum;
            for i := 0 to newInternal.keynum {
                newInternal.keys[i] := tempKey[j];
                j := j + 1;
            }
            j := current.keynum + 1;
            for i := 0 to newInternal.keynum + 1 {
                newInternal.children[i] := tempChildren[j];
                j := j + 1;
            }

            if current == root { // again, if previous is 
                var newRoot := new BPTNode.init();
                newRoot.keys[0] := newInternal.keys[0];
                newRoot.children[0] := current;
                newRoot.children[1] := newInternal;
                newRoot.is_leaf := false;
                newRoot.keynum := 1;
                root := newRoot;
            } else {
                var parent := FindParent(root, current);
                ShiftLevel(current.keys[current.keynum], parent, newInternal);
            }
        }
    } 
    

    method FindParent(current: BPTNode, child: BPTNode) returns (parent: BPTNode?) 
        requires Well()
        requires current.well()
        ensures Well()
        decreases current.height
    /* {
        if current.is_leaf || current.children[0].is_leaf {
            return null;
        }

        for i := 0 to current.keynum + 1 {
            if current.children[i] == child {
                parent := current;
                return parent;
            } else {
                assert current.well() ==> current.children[i].well();
                parent := FindParent(current.children[i], child);
                if parent != null {
                    return parent;
                }
            }
        }
        return null;
    } */
    {
        if current.is_leaf || current.children[0].is_leaf {
            return null;
        }

        parent := null; // Initialize parent to null

        var i := 0;
        while i <= current.keynum && parent == null 
            decreases current.keynum - i // Ensure a decreasing loop variant
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
            while i <= current.keynum && parent == null
                decreases current.keynum - i // Ensure a decreasing loop variant
            {
                assert current.children[i].well();
                parent := FindParent(current.children[i], child);
                i := i + 1;
            }
        }
    
        return parent;
    }

    method Main()
        modifies this
    {
        // Create a new BPTree instance
        var tree := new BPTree.Init();
    
        // Insert a value into the tree
        tree.Insert(42);

        // Verify that the value is in the Contents
        assert 42 in tree.Contents;

        print("Test passed: Value 42 added to the root.");

    } 

    ghost predicate Well()
        reads * // TODO see if this is possible to reduce
    {
        // this in Repr &&
        (root == null ==> Contents == {}) && 
        (root != null ==> 
            root in Repr && root.Repr <= Repr &&
            root.well() &&
            Contents == root.Contents)
    }

}