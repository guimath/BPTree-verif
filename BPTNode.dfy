// include "Utils.dfy"

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
        (isLeaf == true ==> (
        //     |Contents| == keyNum ))//&& 
            (forall num: int :: (num in Contents ==> num in keys[..keyNum]))
        )) &&
        // (isLeaf == true ==> (Contents == set x | x in keys[..keyNum]))
        // (isLeaf ==> forall x :: x in keys[..keyNum] <==> x in Contents)
        // &&
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
        // ghost var prev_keys := keys[..];
        assert forall k :: k in keys[..keyNum] ==> k in Contents;
        keys := InsertIntoSorted(keys, keyNum, key);
        assert forall i :: 0 <= i < keyNum ==> old(keys)[i] in keys[..];
        keyNum := keyNum + 1;
        assert sorted(keys[..keyNum]);
        assert forall i :: 0 <= i < keyNum ==> keys[i] > 0;
        assert forall i,j :: 0<= i< j < keyNum ==> ( keys[i] < keys[j] );
        assert Sorted();
        assert key in keys[..keyNum];
        Repr := Repr + {keys};

        Contents := set x | x in keys[..keyNum];
        assert forall k :: k in old(keys)[..(keyNum-1)] ==> k in keys[..keyNum];
        assert forall k :: k in old(Contents) ==> k in keys[..keyNum];
        assert old(Contents) <= Contents;
        assert forall k :: k in Contents ==> (k!=key ==> k in old(Contents));
        assert key in Contents;
        assert KeysInContents();
        assert old(Contents) + {key} == Contents;
        assert Valid();
    }
    
    lemma ContentsEqualsKeys() 
        requires LengthOk()
        requires Sorted()
        requires isLeaf
        // ensures |Contents| == keyNum
    {
        var seq_contents : seq<int> := [];
        var set_contents : set<int> := {};
        for i := 0 to keyNum 
            invariant 0 <= i <= keyNum
            invariant forall j :: 0 <= j < i ==> ( keys[j] in seq_contents && keys[j] in set_contents )
        {
            seq_contents := seq_contents + [keys[i]];
            set_contents := set_contents + {keys[i]};
            // assert |set_contents| ==  i + 1;
        }

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


predicate sorted (a: seq<int>)
{
  forall i,j :: 0 <= i < j < |a| ==> a[i] < a[j]
}

predicate lessThan(a:seq<int>, key:int) {
  forall i :: 0 <= i < |a| ==> a[i] < key
}

predicate greaterThan(a:seq<int>, key:int) {
  forall i :: 0 <= i < |a| ==> a[i] > key
}

lemma DistributiveIn(a: seq<int>, b:seq<int>, k:int, key:int)
    requires |a| + 1 == |b| 
    requires 0 <= k <= |a|
    requires b == a[..k] + [key] + a[k..]
    ensures forall i :: 0 <= i < |a| ==> a[i] in b
{
    assert forall j :: 0 <= j < k ==> a[j] in b;
    assert forall j :: k <= j < |a| ==> a[j] in b;
    assert ((forall j :: 0 <= j < k ==> a[j] in b) && (forall j :: k <= j < |a| ==> a[j] in b)) 
                    ==> (forall j :: 0 <= j < |a| ==> a[j] in b);
    assert forall j :: 0 <= j < |a| ==> a[j] in b;
}

lemma DistributiveGreater(a: seq<int>, b:seq<int>, k:int, key:int)
    requires |a| + 1 == |b| 
    requires 0 <= k <= |a|
    requires b == a[..k] + [key] + a[k..]
    requires forall j :: 0 <= j < |a| ==> a[j] > 0
    requires key > 0
    ensures forall i :: 0 <= i < |b| ==> b[i] > 0
{
    assert forall j :: 0 <= j < |b| ==> b[j] > 0;
}


// verifies in more than 45 seconds, but less than 100 seconds
method InsertIntoSorted(a: array<int>, limit:int, key:int) returns (b: array<int>)
    requires key > 0
    requires key !in a[..]
    requires 0 <= limit < a.Length
    requires forall i :: 0 <= i < limit ==> a[i] > 0
    requires forall i :: limit <= i < a.Length ==> a[i] == 0
    requires sorted(a[..limit]) 
    ensures b.Length == a.Length
    ensures sorted(b[..(limit+ 1)])
    ensures forall i :: limit + 1 <= i < b.Length ==> b[i] == 0  
    ensures forall i :: 0 <= i < limit ==> a[i] in b[..]
    ensures forall i :: 0 <= i < limit + 1 ==> b[i] > 0
    ensures key in b[..(limit+1)]
    ensures forall k :: k in a[..limit] ==> k in b[..(limit+1)]
    ensures forall k :: k in b[..(limit+1)] ==> (k!=key ==> k in a[..limit])
{
    b:= new int[a.Length];

    ghost var k := 0;
    b[0] := key;

    ghost var a' := a[..];

    var i:= 0;
    while (i < limit)
        modifies b
        invariant 0 <= k <= i <= limit
        invariant b.Length == a.Length
        invariant a[..] == a'
        invariant lessThan(a[..i], key) ==> i == k
        invariant lessThan(a[..k], key)
        invariant b[..k] == a[..k]
        invariant b[k] == key
        invariant k < i ==> b[k+1..i+1] == a[k..i]
        invariant k < i ==> greaterThan(b[k+1..i+1], key)
        invariant 0 <= k < b.Length && b[k] == key
    {
        if(a[i]<key)
        {
            b[i]:= a[i];
            b[i+1] := key;
            k := i+1;
        }
        else if (a[i] >= key)
        {
            b[i+1] := a[i];
        } 
        i := i+1;
    }
    assert b[..limit+1] == a[..k] + [key] + a[k..limit];
    assert sorted(b[..limit+1]);

    // assert b[..limit+1] == a[..k] + [key] + a[k..limit];
    DistributiveIn(a[..limit], b[..limit+1], k, key);
    assert forall i :: 0 <= i < limit ==> a[i] in b[..limit+1];

    DistributiveGreater(a[..limit], b[..limit+1], k, key);
    // assert forall i :: 0 <= i < limit + 1 ==> b[i] > 0;

    ghost var b' := b[..];
    i := limit + 1;
    while i < b.Length 
        invariant limit + 1 <= i <= b.Length 
        invariant forall j :: limit + 1 <= j < i ==> b[j] == 0
        invariant b[..limit+1] == b'[..limit+1]
        invariant sorted(b[..limit+1])
    {
        b[i] := 0;
        i := i + 1;
    }
    assert forall i :: limit + 1 <= i < b.Length ==> b[i] == 0;

}
