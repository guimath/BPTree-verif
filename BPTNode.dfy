
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

    // ghost set for verifivation
    ghost var Contents: set<int>  
    ghost var Repr: set<object>

    ghost predicate Valid()
        reads * // TODO I think this should be reduced
        decreases height
        ensures Valid() ==> this in Repr
    {
        this in Repr && 
        height >= -1 && // bottom limit 
        LengthOk() &&
        Sorted()&&
        LeavesHeightEq() && 
        KeysInRepr() &&
        (isLeaf==false ==> (
            ChildNum() &&
            ChildrenInRepr() &&
            ChildHeightEq() &&
            Hierarchy() &&
            NonCyclical() &&
            (forall i: int :: 0 <= i < keyNum+1 ==> (
                children[i] != null ==> (children[i].Valid() && 
                    children[i] in Repr && children[i].Repr <= Repr && // TODO maybe not needed because of ChildrenInRepr
                    children[i].Contents <= Contents) // TODO maybe not needed because of sum of children's contents
            )) && 
            (keyNum > 0 ==> (Contents == SumOfChildContents(children[0..keyNum])))
        )) 
    }


    ghost function SumOfChildContents(children: seq<BPTNode>): set<int>
        reads children 
    {
        if children == [] then {}
        else children[0].Contents + SumOfChildContents(children[1..])
    }

    // ################ For all nodes ################
    // - MinKeys : must contain at least floor(n/2) keys.
    
    ghost predicate Sorted()
        //keys are Sorted from left two right
        reads this, keys, children
        requires LengthOk()
    {
        forall i: int :: 0 <= i < keyNum-1 ==> (
            keys[i] < keys[i+1]
        )
    }
    ghost predicate LeavesHeightEq()
        // all leaves are at the same distance from the root (always -1).
        reads this
    {
        isLeaf <==> height==-1
    }

    // ################ For internal nodes ################
    ghost predicate ChildNum()
        // contains one more child than it has keys. 
        reads this, Repr, keys, children
        requires isLeaf==false
        requires LengthOk()
    {
        // enough values
        (forall i: int :: 0 <= i < keyNum ==> (
            keys[i] > 0 && 
            children[i] is BPTNode
        )) &&
        children[keyNum] is BPTNode &&
        // no more values
        (keyNum < ORDER ==> keys[keyNum] == 0) &&
        (forall i: int :: keyNum < i < ORDER ==> (
            keys[i] == 0 && 
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
        reads this, Repr, children
        requires LengthOk()
    {
        forall i: int :: 0 <= i < keyNum+1 ==> ( children[i] != null ==> (children[i] in Repr && children[i].Repr <= Repr ))
    }   

    ghost predicate KeysInRepr()
        reads this, Repr
        requires LengthOk()
    {
        keys in Repr
    } 

    ghost predicate Hierarchy()
        // all keys in a given subtree are bounded by surrounding keys in parent node.
        reads this, Repr, children, keys
        requires isLeaf==false
        requires LengthOk()
        requires ChildrenInRepr()
        requires ChildNum()
    {
        forall i: int :: 0 <= i < keyNum+1 ==> (
            (forall k :: k in children[i].Contents ==> (
                (i > 0 ==> keys[i-1] < k) &&
                (i< keyNum ==> k <= keys[i])
            ))
        )
    }

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

    constructor Init()
        ensures children.Length == ORDER + 1
        ensures keys.Length == ORDER
        ensures keyNum==0
        ensures height==-1
        ensures isLeaf==true
        ensures Empty()
        ensures Valid() 
        ensures fresh(Repr - {this})
        //ensures Valid() && Well() && fresh(Repr - {this})
        ensures Contents == {}
        //ensures Repr == {this}
        ensures fresh(Repr - {this})

    {
        isLeaf := true;
        height := -1;
        keyNum := 0;
        children := new BPTNode?[ORDER + 1][null, null, null, null, null, null];
        keys := new int[ORDER][0, 0, 0, 0, 0];
        Contents := {};
        Repr := {this} + {keys} + {children}; 
        
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