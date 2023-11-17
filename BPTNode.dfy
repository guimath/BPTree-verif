
const ORDER:int := 5

class BPTNode {
    // array of length ORDER
    var keys: array<int>
    // array of length ORDER + 1
    var children: array<BPTNode?>
    // number of keys active
    var keyNum: int
    // height
    var height: int
    // is leaf
    var isLeaf: bool 
    // pointer towards next leaf
    var nextLeaf : BPTNode?

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

    ghost predicate HalfFull()
        reads this, Repr
        requires Valid()
    {
        keyNum > ORDER/2 &&
        isLeaf == false ==>
            forall i:int :: 0<= i < keyNum ==> children[i].HalfFull()
    }

    //sequence version
    ghost function SumOfChildContents(childrenSeq: seq<BPTNode>): set<int>
        reads childrenSeq
        decreases |childrenSeq|
        ensures |childrenSeq| > 0 ==> 
            SumOfChildContents(childrenSeq) == childrenSeq[0].Contents + SumOfChildContents(childrenSeq[1..])
    {
        if childrenSeq == [] then {}
        else childrenSeq[0].Contents + SumOfChildContents(childrenSeq[1..])
    }

    // index version
    ghost function SumOfChildrenContents(start: int, end: int): set<int>
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

    ghost predicate ChildrenContentsDisjoint() 
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

    // ################ For all nodes ################
    // - MinKeys : must contain at least floor(n/2) keys.
    
    ghost predicate Sorted()
        //keys are Sorted from left two right
        reads this, keys
        requires LengthOk()
    {
        (forall i: int :: 0 <= i < keyNum-1 ==> (
            keys[i] < keys[i+1]
        )) && 
        (forall i: int :: 0 <= i < keyNum-1 ==> ( // additional condition to help compiler
            keys[i] < keys[keyNum-1]
        )) 
    }
    ghost predicate LeavesHeightEq()
        // all leaves are at the same distance from the root (always -1).
        reads this
    {
        isLeaf <==> height==-1
    }

    ghost predicate KeyNumOK()
        // contains one more child than it has keys. 
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
    // ################ For internal nodes ################

    ghost predicate ChildNum()
        // contains one more child than it has keys. 
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

    ghost predicate ChildHeightEq()
        // all subtrees must be the same height. 
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

    ghost predicate ChildrenInRepr()
        reads this, Repr
        requires isLeaf == false
        requires LengthOk()
        // requires ChildNum()
    {
        children in Repr &&
        forall i: int :: 0 <= i < keyNum+1 ==> ( children[i] in Repr && children[i].Repr <= Repr )
    }   

    ghost predicate KeysInRepr()
        reads this, Repr
        requires LengthOk()
    {
        keys in Repr
    } 

    ghost predicate KeysInContents()
        reads this, Repr
        requires LengthOk()
        requires KeysInRepr()
    {
        (isLeaf == true ==> (
            |Contents| == keyNum && 
            (forall num: int :: (num in Contents ==> num in keys[..keyNum]))
        )) &&
        forall i : int :: 0 <= i < keyNum ==> (
            keys[i] in Contents
        )
    }

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

 /*   PROBLEM WITH THIS: cannot read children[i].isLeaf beacuse it is not in Repr. I do not want to add it to Repr because then I lose nice properties
      ==> this is why could be better to add this as a separate variable
    ghost predicate LeafConnected()
        reads this, Repr, children
        requires LengthOk()
        requires isLeaf==true
    {
        forall i: int :: 0 <= i < ORDER ==> (
            (i == keyNum ==> (children[i] != null ==> (children[i] is BPTNode && children[i].isLeaf == true ))) &&
            (i != keyNum ==> children[i] == null)
        )
    } */

    // ################ for leaves ################

    // - LinkedLeaves : contains extra pointer towards the next leaf.
    // - AllKeysInLeaves : all keys appear in a leaf node.


    // ################ generic ################
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
        children[ORDER] == null
    }

    ghost predicate NotFull()
        reads this
    {
        keyNum < ORDER
    }
    
    ghost predicate ContainsVal(val: int) 
        reads this
    {
        val in Contents
    }

    method GetInsertIndex(key:int) returns (idx:int)
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
        requires Valid()
        requires isLeaf == true 
        requires NotFull() 
        requires !(key in Contents)
        requires key > 0
        modifies this, keys
        ensures Valid()
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
        AddKeysContent();
    }

    ghost method AddKeysContent()
        modifies this
        requires ValidBeforeContentUpdate()
        ensures Valid()
    {
        // Contents := {}
        // for j:int := 0  to keyNum 
        // {
        //     Contents := Contents + {keys[j]};
        // }
        //TODO Patch
        assume KeysInRepr();
        assume KeysInContents();
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
    {
        isLeaf := true;
        height := -1;
        keyNum := 0;
        children := new BPTNode?[ORDER + 1][null, null, null, null, null, null];
        keys := new int[ORDER][0, 0, 0, 0, 0];
        Contents := {};
        Repr := {this} + {keys} + {children}; 
        nextLeaf := null;
        
        // Hardcoded rather than loop because weird error :
        // "in the first division of the constructor body (before 'new;'), 
        // 'this' can only be used to assign to its fields"
        // When running this loop
        // for i := 0 to ORDER - 1 {
        //     keys[i] := 0;
        //     children[i] := null;
        // }
        // children[ORDER] := null;

    }

}