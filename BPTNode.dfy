include "utils.dfy"

const ORDER:int := 5

class BPTNode {
    var keys: array<int>
    // array of length ORDER
    var children: array<BPTNode?>
    // array of length ORDER + 1
    var keyNum: int
    // number of active keys 
    var height: int
    // height
    var isLeaf: bool 
    // wether node is a leaf
    var nextLeaf : BPTNode?
    // pointer towards next leaf

    // ghost set for verifivation
    ghost var Contents: set<int>  
    ghost var Repr: set<object>

        // ( keyNum > 0 ==> !Empty() ) &&
    ghost predicate Valid()
        reads this, Repr
        decreases height
        ensures Valid() ==> this in Repr
    {
        this in Repr && 
        height >= -1 &&
        LengthOk() &&
        KeysInRepr() &&
        KeysInContents() &&
        children in Repr &&
        ( keyNum == 0 ==> Empty()) &&
        KeyNumOK()&&
        Sorted()&&
        LeavesHeightEq() && 
        (isLeaf==false ==> (
            nextLeaf == null &&
            ChildrenInRepr() &&
            ChildNum() &&
            ChildHeightEq() &&
            Hierarchy() &&
            NonCyclical() &&
            ChildrenContentsDisjoint() &&
            (forall i: int :: 0 <= i < keyNum+1 ==> ( 
                children[i].keys in Repr && 
                children[i].children in Repr && 
                children[i].Valid() && 
                children[i].Contents <= Contents)
            ) && 
            (keyNum > 0 ==> (
                Contents == SumOfChildContents(children[0..keyNum+1]) && 
                (forall num: int :: (num in Contents ==> num in SumOfChildContents(children[0..keyNum+1])))
            ))
        )) 
    }

          //  && (forall val: int :: val in Contents ==> (exists j: int :: 0 <= j <= keyNum && val in children[j].Contents))))
    ghost predicate ValidBeforeContentUpdate()
        reads this, children, keys, Repr
        decreases height
        // ensures Valid() ==> this in Repr
    {
        this in Repr && 
        height >= -1 &&
        LengthOk() &&
        children in Repr &&
        ( keyNum == 0 ==> Empty() ) &&
        KeyNumOK()&&
        Sorted()&&
        LeavesHeightEq() && 
        (isLeaf==false ==> (
            nextLeaf == null &&
            ChildrenInRepr() &&
            ChildNum() &&
            ChildHeightEq() &&
            Hierarchy() &&
            NonCyclical() &&
            ChildrenContentsDisjoint() &&
            (forall i: int :: 0 <= i < keyNum+1 ==> ( 
                children[i].keys in Repr && 
                children[i].children in Repr && 
                children[i].Valid() && 
                children[i].Contents <= Contents)
            ) && 
            (keyNum > 0 ==> (
                Contents == SumOfChildContents(children[0..keyNum+1]) && 
                (forall num: int :: (num in Contents ==> num in SumOfChildContents(children[0..keyNum+1])))
            ))
        )) 
    }
    // ************************************************ //
    // ************** ORDERED PREDICATES ************** //
    // ************************************************ //

    ghost predicate HalfFull()
        // all non root nodes in subtree contains more than ORDER/2 keys
        reads this, Repr
        requires Valid()
    {
        keyNum > ORDER/2 &&
        isLeaf == false ==>
            forall i:int :: 0<= i < keyNum ==> children[i].HalfFull()
    }

    ghost predicate KeyNumOK()
        // contains exactly keyNum keys 
        reads this, Repr, keys, children
        requires LengthOk()
    {
        // enough values
        (forall i: int :: 0 <= i < keyNum ==> (
            keys[i] > 0
        )) &&
        // no more values
        (forall i: int :: keyNum <= i < ORDER ==> (
            keys[i] == 0
        ))
    }

    ghost predicate ChildNum()
        // contains one more child than it has keys (keyNum +1). 
        reads this, Repr, keys, children
        requires isLeaf==false
        requires LengthOk()
    {
        // enough values
        (forall i: int :: 0 <= i <= keyNum ==> (
            children[i] is BPTNode
        )) &&
        // no more values
        (forall i: int :: keyNum < i <= ORDER ==> (
            children[i] == null
        ))
    }

    // ************************************************ //
    // ************** BALANCED PREDICATES ************* //
    // ************************************************ //

    ghost predicate ChildHeightEq()
        // all children must be the same height. 
        reads this, Repr, children, keys
        requires isLeaf==false
        requires LengthOk()
        requires ChildNum()
        requires ChildrenInRepr()
    {   
        (forall i: int :: 0 <= i < keyNum+1 ==> (
            children[i].height == height -1
        ))
    }

    ghost predicate LeavesHeightEq()
        // all leaves are at the same distance from the root (always -1).
        reads this
    {
        isLeaf <==> height==-1
    }

    // ************************************************ //
    // ************* ALIGNEMENT PREDICATES ************ //
    // ************************************************ //

    ghost predicate Hierarchy()
        // all keys in a given subtree are bounded by surrounding keys in parent node.
        reads this, Repr, children, keys
        requires isLeaf==false
        requires LengthOk()
        requires ChildNum()
        requires ChildrenInRepr()
    {
        forall i: int :: 0 <= i < keyNum+1 ==> (
            (forall k :: k in children[i].Contents ==> (
                (i > 0 ==> keys[i-1] <= k) &&
                (i< keyNum ==> k < keys[i])
            ))
        )
    }

    ghost predicate Sorted()
        //keys are Sorted from left two right
        reads this, keys
        requires LengthOk()
    {
        (forall i,j :: 0<= i< j < keyNum ==> (
            keys[i] < keys[j]
        ))
    }

    // ************************************************ //
    // *************** HELPER PREDICATES ************** //
    // ************************************************ //

    ghost predicate LengthOk()
        // the keys and children array are Well formed
        reads this
    {
        keys.Length == ORDER &&
        children.Length == ORDER+1 &&
        keyNum < ORDER + 1 &&
        keyNum >= 0 
    }

    ghost predicate Empty()
        // the keys and children array are Empty
        reads this, children, keys
        requires LengthOk()
    {
        (forall i: int :: 0 <= i < ORDER ==> (
            children[i]==null &&
            keys[i]==0
        )) &&
        children[ORDER] == null &&
        |Contents| == 0
    }

    ghost predicate NotFull()
        // not all keys are occupied
        reads this
    {
        keyNum < ORDER
    }
    
    ghost predicate ContainsVal(val: int) 
        // val in the subtree
        reads this
    {
        val in Contents
    }


    // ************************************************ //
    // *************** GHOST PREDICATES *************** //
    // ************************************************ //

    ghost predicate ChildrenInRepr()
        //children array in repr and all children Repr in Repr 
        reads this, Repr
        requires isLeaf == false
        requires LengthOk()
        // requires ChildNum()
    {
        children in Repr &&
        forall i: int :: 0 <= i < keyNum+1 ==> ( children[i] in Repr && children[i].Repr <= Repr )
    }   

    ghost predicate KeysInRepr()
        //keys array in repr
        reads this, Repr
        requires LengthOk()
    {
        keys in Repr
    } 

    ghost predicate KeysInContents()
        // all keys in Contents and if leaf all Content are keys
        reads this, Repr
        requires LengthOk()
        requires KeysInRepr()
    {
        // this part removed because it was hard to verify set size...
        // (isLeaf == true ==> (
        //     // |Contents| == keyNum && 
        //     (forall num: int :: (num in Contents ==> num in keys[..keyNum]))
        // )) &&
        (isLeaf == true ==> (Contents == set x | x in keys[..keyNum]))
        &&
        forall i : int :: 0 <= i < keyNum ==> (
            keys[i] in Contents
        )
    }

    ghost predicate ChildrenContentsDisjoint() 
        // Keys of children subtrees are disjoint
        reads this, Repr, children, keys
        requires isLeaf==false
        requires LengthOk()
        requires ChildNum()
        requires ChildrenInRepr()
    {
        forall i:int :: 0 <= i < keyNum ==> (
            forall j: int :: i < j <= keyNum ==> (
                children[i].Contents !! children[j].Contents
            )
        )
    }

    ghost predicate NonCyclical()
        // no node can be contain cyclical link   
        reads this, Repr, children, keys
        requires isLeaf==false
        requires LengthOk()
        requires ChildNum()
        requires ChildrenInRepr()
    {
        (forall i: int :: 0 <= i < keyNum+1 ==> (
            this !in children[i].Repr
        ))
    }
    ghost function SumOfChildContents(childrenSeq: seq<BPTNode>): set<int>
        //sequence version of getting all Contents of child
        reads childrenSeq
        decreases |childrenSeq|
        ensures |childrenSeq| > 0 ==> 
            SumOfChildContents(childrenSeq) == childrenSeq[0].Contents + SumOfChildContents(childrenSeq[1..])
    {
        if childrenSeq == [] then {}
        else childrenSeq[0].Contents + SumOfChildContents(childrenSeq[1..])
    }

    ghost function SumOfChildrenContents(start: int, end: int): set<int>
        // index version of getting all Contents of child
        reads this, Repr, children, keys
        requires isLeaf == false
        requires LengthOk()
        requires ChildNum()
        requires ChildrenInRepr()
        requires 0 <= start 
        requires end <= keyNum + 1
        decreases end - start
    {
        if start >= end then {}
        else if start > keyNum then {}
            else children[start].Contents + SumOfChildrenContents(start+1, end)
    }

    // ************************************************ //
    // ******************* METHODS ******************** //
    // ************************************************ //

    method GetInsertIndex(key:int) returns (idx:int)
        // get first index where key < keys[idx]
        requires Valid() 
        requires !(key in Contents)
        ensures 0<= idx <= keyNum 
        ensures idx > 0 ==> keys[idx-1]< key
        ensures idx < keyNum ==> key < keys[idx]
        ensures Valid()
    {
        idx := keyNum;
        for i := 0 to keyNum 
            invariant i>0 ==> key > keys[i-1]
            // invariant i == idx ==> key < keys[i]
        {
            if key < keys[i] {
                idx := i;
                break;
            }
        }      
    }
    
    method InsertAtLeaf(key:int) 
        // insert a key value in a node
        requires Valid()
        requires isLeaf == true 
        requires NotFull() 
        requires !(key in Contents)
        requires key > 0
        modifies this, keys
        ensures Valid()
        ensures ContainsVal(key)
        ensures old(Contents) + {key} == Contents
    {

        var idx := GetInsertIndex(key);
        ghost var prev_keys := keys[..];
        if keyNum > 0 {
            assert idx < keyNum ==> key < keys[idx];
            assert 0< idx < keyNum ==> keys[idx-1] < key;
            // shifting
            if idx < keyNum {
                var i:=keyNum-1;
                ghost var rep_key := keys[idx];

                while idx <= i
                    modifies keys 
                    invariant idx-1<= i 
                    invariant (0 <= idx < keyNum) ==> key < keys[idx]
                    invariant (0 <  idx < keyNum) ==> keys[idx-1] < key
                    invariant rep_key == keys[idx] 
                    invariant forall j: int :: 0 <= j < idx ==> (
                        keys[j] < keys[j+1]
                    )   
                    invariant forall j: int :: 0 <= j <= i ==> ( // i = idx -1 
                        keys[j] == prev_keys[j] // untouched part of array
                    )   
                    invariant forall j: int :: i < j < keyNum ==> ( // end : i = idx -1 
                        keys[j+1] == prev_keys[j]
                    )  
                    invariant forall j: int :: keyNum < j < ORDER ==> ( // end : i = idx -1 
                        keys[j] == 0
                    )  
                {
                    keys[i+1] := keys[i];
                    i := i-1;
                }

                assert i == idx -1;
                assert forall j: int :: idx < j < keyNum ==> ( 
                    keys[j] == prev_keys[j-1]
                );
                // assert  keys[0..idx] == prev_keys[0..idx];
                // assert  keys[idx+1..keyNum] == prev_keys[idx..keyNum-1];
                assert forall j: int :: idx < j < keyNum ==> ( // previous array was sorted so this is also
                    prev_keys[j-1] < prev_keys[j]
                );   
                assert forall j: int :: idx < j < keyNum ==> ( // previous array was sorted so this is also
                    keys[j] < keys[j+1]
                );   
            }
        }
        keys[idx] := key;
        assert forall j: int :: 0 <= j < idx ==> ( //first part sorted
            keys[j] < keys[j+1] 
        );   
        assert forall j: int :: idx < j < keyNum ==> ( //sec part sorted
            keys[j] < keys[j+1]
        );   
        assert 0 < idx ==> keys[idx-1]< keys[idx]; // idx larger than prev
        assert idx < keyNum ==> keys[idx] < keys[idx+1]; // idx bigger then next
        keyNum := keyNum+1; 


        // NEWEST COMMENT: here is the problem with updating Contents
        // Dafny does not seem to understand that when we add new key Contents contains all the keys
        // (we are still in process of separating the insert in an array into a separate function)

        assert key !in Contents;
        Contents := Contents + {key};
        // TODO delete
        // assert Valid();
        // AddKeysContent();
        assert old(Contents) + {key} == Contents;
        // assert (set x | x in prev_keys[..(keyNum-1)]) == old(Contents);
        // assert (set x | x in prev_keys[..(keyNum-1)]) + {key} == (set x | x in keys[..keyNum]);
        assert Contents == set x | x in keys[..keyNum]; //may not hold
        assert KeysInContents(); // may not hold
        assert Valid();
    }

    // TODO prob delete
    ghost method AddKeysContent()
        // Adds all keys to the content 
        // only for leaves 
        modifies this
        requires ValidBeforeContentUpdate()
        requires keyNum > 0
        requires isLeaf
        ensures Valid()
    {
        assert this in Repr;
        assert children in Repr;
        Repr := Repr + {keys};
        assert children in Repr;
        assert KeysInRepr();
        assert this in Repr;
        // Contents := set x | x in keys[..keyNum] :: x;
        // Contents := {};
        // for i := 0 to keyNum 
        //     invariant KeysInRepr()
        //     invariant this in Repr
        //     invariant children in Repr
        //     invariant Sorted()
        //     // invariant Repr == old(Repr) // QUESTION : why does this not hold 
        //     invariant i < keyNum ==> forall j :: 0 < j < i ==> keys[j] < keys[i]
        //     invariant i < keyNum ==> forall j :: 0 < j < i ==> keys[j] != keys[i]
        //     invariant forall j :: 0 <= j < i ==> keys[j] in Contents
        //     // invariant |Contents| == i // COMMENT : needed if checking length in keysInContent
        //     { 
        //         Contents := Contents + {keys[i]}; 
        //     }

        Contents := set x | x in keys[..keyNum];

        assert KeysInContents();
        assert isLeaf;
        assert children in Repr;
        assert Valid();
    }

    constructor Init()
        ensures children.Length == ORDER + 1
        ensures keys.Length == ORDER
        ensures keyNum==0
        ensures height==-1
        ensures isLeaf==true
        ensures Empty()
        ensures Valid() 
        ensures fresh(Repr - {this})
        ensures Contents == {}
        ensures nextLeaf == null
    {
        isLeaf := true;
        height := -1;
        keyNum := 0;
        children := new BPTNode?[ORDER + 1](i => null);
        keys := new int[ORDER](i => 0);
        Contents := {};
        Repr := {this} + {keys} + {children}; 
        nextLeaf := null;
    }

}