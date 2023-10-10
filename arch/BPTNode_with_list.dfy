
class BPTNode {
    const MAX_KEYS := 5
    ghost var Contents: set<int>
    ghost var Repr: set<BPTNode>

    var keys: array<int>
    var children: array<BPTNode?>

    var keynum: int
    var height: int
    var is_leaf: bool

    ghost predicate Well() 
    // number of keys correct (doesn't exceed limit)
        reads * 
        decreases height + 1
    {   
        height >=-1 &&
        children.Length == MAX_KEYS &&
        keynum < MAX_KEYS &&
        (is_leaf==true ==> keynum<=MAX_KEYS) &&
        (is_leaf==false ==> keynum<=MAX_KEYS-1) &&
        (forall i: int :: 0 <= i < keynum ==> (
            children[i] is BPTNode &&
            children[i].height +1 == height &&
            children[i].Well()
        ))
    }

    ghost predicate LessWell()
        reads * // this, children, keys
    {
        keynum < MAX_KEYS &&
        Valid() && 
        (forall i: int :: 0 <= i < keynum ==> (
            children[i].height +1 == height &&
            children[i].Well()
        ))
    }   

    ghost predicate ChildLessWell(pos:int,child:BPTNode)
        requires child in this.Repr
        reads * //this, children, child
    {
        pos < children.Length && pos>0 && 
        children.Length == MAX_KEYS &&
        keynum < MAX_KEYS &&
        Valid() &&
        keynum <= MAX_KEYS-1 &&
        child.height == height-1 &&
        is_leaf==false &&
        (forall i: int :: 0 <= i < keynum ==> (i!= pos ==> children[i].Well())) &&
        child.LessWell() &&
        child == children[pos]
    }

    predicate sortkey()
        reads this, keys
        requires keys.Length == MAX_KEYS
        requires keynum < MAX_KEYS
    { 
        (forall i: int :: 1 <= i < keynum ==> keys[i-1] <= keys[i])
    }

    // predicate ContainingKey()
    //     reads this
    //   {
    //     (keynum==0 ==> Contents =={})&&   
    //     (keynum==1 ==> Contents =={key_1}) &&
    //     (keynum==2 ==> Contents =={key_1,key_2}) &&
    //     (keynum==3 ==> Contents =={key_1,key_2,key_3}) &&
    //     (keynum==4 ==> Contents =={key_1,key_2,key_3,key_4}) &&
    //     (keynum==5 ==> Contents =={key_1,key_2,key_3,key_4,key_5}) 
    //   } 

    // predicate newParent()
    //     reads this, Repr
    //   {
    //     this in Repr &&
    //     child_1 !=null && child_2==null && child_3==null && child_4==null &&
    //     key_1 ==0 && key_2 ==0 && key_3 ==0 && key_4 ==0 && keynum == 0 &&
    //     ( child_1 in Repr &&
    //       child_1.Repr <= Repr && this !in child_1.Repr && 
    //       child_1.Valid() && height == child_1.height+1) && 
    //       Contents == child_1.Contents
    //   }
    
    ghost predicate Valid()
        reads * //,child_1,child_2,child_3,child_4
        //requires this in Repr
        decreases height + 1
    {
        keynum < MAX_KEYS &&
        children.Length == MAX_KEYS &&
        keys.Length == MAX_KEYS &&
        height >=-1 &&
        keynum>=0 &&
        sortkey() && 
        (forall i: int :: 0 <= i < keynum ==> (
            children[i] is BPTNode &&
            children[i] in Repr &&
            children[i].Repr <= Repr && 
            this !in children[i].Repr && 
            children[i].height +1 == height &&
            children[i].Valid()
        )) && 
        // lowest height is always leaf
        ((height==-1) <==> (is_leaf == true)) && 
        ((is_leaf == true) ==> (
            keynum < MAX_KEYS && 
            Repr == {this} && 
            //ContainingKey() &&
            (forall i: int :: 0 <= i < MAX_KEYS ==> children[i]==null)
        )) &&

        ((is_leaf == false) ==> (
            height>=0 &&
            (forall i: int :: 0 <= i < keynum ==> (
                // has the children required
                children[i]!=null
                // TODO TEST content is sum of child contents
            )) &&
            // No other children
            (forall i: int :: keynum <= i < MAX_KEYS ==> children[i]==null)
        )) && 

        
        //disjoint set
        (forall i: int :: 1 <= i < keynum ==> (
            (forall j: int :: 0 <= j < i ==> (children[i].Repr !! children[j].Repr))
        )) 
    
      
    //   ( (child_1 != null) ==>
    //   (key_1 in child_2.Contents && forall y :: y in child_1.Contents ==> y <= key_1) ) &&
    //   ((child_2 != null) ==>
    //   (forall y :: y in child_2.Contents ==> y >= key_1) ) &&
    //   ((child_3 != null) ==>
    //   ((forall y :: y in child_3.Contents ==> y >= key_2) &&
    //   (key_2 in child_3.Contents && forall y :: y in child_2.Contents ==> y <= key_2)) ) &&
    //   ((child_4 != null) ==>
    //   ((forall y :: y in child_4.Contents ==> y >= key_3) &&
    //   (key_3 in child_4.Contents && forall y :: y in child_3.Contents ==> y <= key_3)) )  &&
    //   ((child_MAX_KEYS != null) ==>
    //   ((forall y :: y in child_MAX_KEYS.Contents ==> y >= key_4) &&
    //   (key_4 in child_MAX_KEYS.Contents && forall y :: y in child_4.Contents ==> y <= key_4)) )&&
    }

    predicate Empty()
        requires children.Length == MAX_KEYS
        requires keys.Length == MAX_KEYS
        reads this, children, keys
    {
        (forall i: int :: 0 <= i < MAX_KEYS ==> (
            children[i]==null &&
            keys[i]==0
        ))
    }

    constructor Init()
        ensures children.Length == MAX_KEYS
        ensures keys.Length == MAX_KEYS
        ensures keynum==0
        ensures height==-1
        ensures Valid() && Well() && fresh(Repr - {this})
        ensures Contents == {}
        ensures Repr == {this}

        ensures Empty()
        ensures is_leaf==true
    {
        is_leaf := false;
        is_leaf := true;
        height := -1;
        //TODO use Preproc to change
        children := new BPTNode?[MAX_KEYS][null, null, null, null, null];
        keys := new int[MAX_KEYS][0,0,0,0,0];
        //this.keys[0], this.keys[1], this.keys[2], this.keys[3], this.keys[4] := 0,0,0,0,0;
        // forall (i:int := 0 to MAX_KEYS) {
        //     children[i] = null;
        //     keys[i] = 0;
        // }
        keynum := 0;
        Contents := {};
        Repr := {this};
    }

}