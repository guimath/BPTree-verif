class BPTNode {
    ghost var Contents: set<int>
    ghost var Repr: set<BPTNode>
    
    var keynum: int
    var key_1: int
    var key_2: int
    var key_3: int
    var key_4: int
    var key_5: int

    //Height of the subtree
    var height: int
    var is_leaf: bool
    var child_1: BPTNode?
    var child_2: BPTNode?
    var child_3: BPTNode?
    var child_4: BPTNode?
    var child_5: BPTNode?
  
  predicate Well()
    reads this, Repr
  {
    Valid() &&
    (this.is_leaf==true ==> keynum<=4) &&
    (this.is_leaf==false ==> keynum<=3) &&
    (child_1 != null ==> child_1.Well())&&
    (child_2 != null ==> child_2.Well())&&
    (child_3 != null ==> child_3.Well())&&
    (child_4 != null ==> child_4.Well())
  }
  predicate LessWell()
    reads this, Repr
  {
    Valid() &&
    (child_1 != null ==> child_1.Well())&&
    (child_2 != null ==> child_2.Well())&&
    (child_3 != null ==> child_3.Well())&&
    (child_4 != null ==> child_4.Well())&&
    (child_5 != null ==> child_5.Well())
  }
    predicate ChildLessWell(pos:int,child:BPTNode)
    reads this, Repr
  {
    Valid() &&
    keynum<=3 &&
    child in Repr &&
    child.height == height-1 &&
    is_leaf==false &&
    (keynum ==1 ==> ((child_1.Well()&&child_2.LessWell()&&pos==2&&child == child_2)||(child_1.LessWell()&&child_2.Well()&&pos==1&&child == child_1))) &&
    (keynum ==2 ==> ((child_1.Well()&&child_2.LessWell()&&child_3.Well()&&pos==2&&child == child_2)||(child_1.LessWell()&&child_2.Well()&&child_3.Well()&&pos==1&&child == child_1)||(child_1.Well()&&child_2.Well()&&child_3.LessWell()&&pos==3&&child == child_3))) &&
    (keynum ==3 ==> ((child_1.Well()&&child_2.LessWell()&&child_3.Well()&&child_4.Well()&&pos==2&&child == child_2)||
                    (child_1.LessWell()&&child_2.Well()&&child_3.Well()&&child_4.Well()&&pos==1&&child == child_1)|| 
                    (child_1.Well()&&child_2.Well()&&child_3.LessWell()&&child_4.Well()&&pos==3&&child == child_3)||
                    (child_1.Well()&&child_2.Well()&&child_3.Well()&&child_4.LessWell()&&pos==4&&child == child_4))) 
  } 
  predicate sortkey()
    reads this
  { 
    (keynum>=2 ==> key_2 >= key_1) && 
    (keynum>=3 ==> key_3 >= key_2) &&
    (keynum>=4 ==> key_4 >= key_3) &&
    (keynum==5 ==> key_5 >= key_4) 
  }
  predicate ContainingKey()
    reads this
  {
    (keynum==0 ==> Contents =={})&&   
    (keynum==1 ==> Contents =={key_1}) &&
    (keynum==2 ==> Contents =={key_1,key_2}) &&
    (keynum==3 ==> Contents =={key_1,key_2,key_3}) &&
    (keynum==4 ==> Contents =={key_1,key_2,key_3,key_4}) &&
    (keynum==5 ==> Contents =={key_1,key_2,key_3,key_4,key_5}) 
  } 
  predicate newParent()
    reads this, Repr
  {
    this in Repr &&
    child_1 !=null && child_2==null && child_3==null && child_4==null &&
    key_1 ==0 && key_2 ==0 && key_3 ==0 && key_4 ==0 && keynum == 0 &&
    ( child_1 in Repr &&
      child_1.Repr <= Repr && this !in child_1.Repr && 
      child_1.Valid() && height == child_1.height+1) && 
      Contents == child_1.Contents
  }
  predicate Valid()
    reads this, Repr//,key //,child_1,child_2,child_3,child_4
  {
    this in Repr &&
    height >=-1 &&
    keynum>=0 &&
    ( (child_1 != null) ==>
      (child_1 in Repr &&
      child_1.Repr <= Repr && this !in child_1.Repr && 
      child_1.Valid() ) ) &&
    ((child_2 != null) ==>
      (child_2 in Repr &&
      child_2.Repr <= Repr && this !in child_2.Repr && child_2.height +1 == height && 
      child_2.Valid() ) ) &&
      ((child_3 != null) ==>
      (child_3 in Repr &&
      child_3.Repr <= Repr && this !in child_3.Repr && child_3.height +1 == height && 
      child_3.Valid()  )) &&
      ((child_4 != null) ==>
      (child_4 in Repr &&
      child_4.Repr <= Repr && this !in child_4.Repr && child_4.height +1 == height && 
      child_4.Valid() )) &&
      ((child_5 != null) ==>
      (child_5 in Repr &&
      child_5.Repr <= Repr && this !in child_5.Repr && child_5.height +1 == height && 
      child_5.Valid() )) &&

    ((height==-1) ==> (is_leaf == true))&&
    ((is_leaf == true) ==> (Repr == {this} && child_1 ==null && child_2 ==null && child_3 ==null && child_4 ==null && child_5 ==null &&
    keynum<= 5 && height ==-1  && sortkey() && ContainingKey()) ) &&
    ((is_leaf == false) ==> ( child_1 !=null && child_2!=null && 
      ((child_3 ==null) <==> (keynum == 1 && Contents == child_1.Contents + child_2.Contents)) && 
      ((child_3 !=null && child_4 ==null) <==> (keynum == 2 && Contents == child_1.Contents + child_2.Contents + child_3.Contents)) && 
      ((child_4 !=null && child_5 ==null) <==> (keynum == 3 && Contents == child_1.Contents + child_2.Contents + child_3.Contents + child_4.Contents)) && 
      ((child_5 !=null) <==> (keynum == 4 && Contents == child_1.Contents + child_2.Contents + child_3.Contents + child_4.Contents + child_5.Contents)) && 
      sortkey() && height>=0 &&
      ( (child_1 != null) ==>
      (key_1 in child_2.Contents && forall y :: y in child_1.Contents ==> y <= key_1) ) &&
      ((child_2 != null) ==>
      (forall y :: y in child_2.Contents ==> y >= key_1) ) &&
      ((child_3 != null) ==>
      ((forall y :: y in child_3.Contents ==> y >= key_2) &&
      (key_2 in child_3.Contents && forall y :: y in child_2.Contents ==> y <= key_2)) ) &&
      ((child_4 != null) ==>
      ((forall y :: y in child_4.Contents ==> y >= key_3) &&
      (key_3 in child_4.Contents && forall y :: y in child_3.Contents ==> y <= key_3)) )  &&
      ((child_5 != null) ==>
      ((forall y :: y in child_5.Contents ==> y >= key_4) &&
      (key_4 in child_5.Contents && forall y :: y in child_4.Contents ==> y <= key_4)) )&&
      ((child_2 != null) ==> (child_2.Repr !! child_1.Repr) )&&
      ((child_3 != null) ==> (child_3.Repr !! child_1.Repr) && (child_3.Repr !! child_2.Repr))&&
      ((child_4 != null) ==> (child_4.Repr !! child_1.Repr) && (child_4.Repr !! child_2.Repr) && (child_4.Repr !! child_3.Repr))&&
      ((child_5 != null) ==> (child_5.Repr !! child_1.Repr) && (child_5.Repr !! child_2.Repr) && (child_5.Repr !! child_3.Repr) && (child_5.Repr!! child_4.Repr)) ) ) 
  }
 

    constructor Init()
        ensures Valid() && Well() && fresh(Repr - {this})
        ensures Contents == {}
        ensures Repr == {this}
        ensures keynum==0
        ensures height==-1
        ensures child_1 == null
        ensures child_2 == null
        ensures child_3 == null
        ensures child_4 == null
        ensures child_5 == null
        ensures key_1 == 0
        ensures key_2 == 0
        ensures key_3 == 0
        ensures key_4 == 0
        ensures key_5 == 0
        ensures is_leaf==true
    {
        is_leaf := true;
        height := -1;
        child_1 :=null;
        child_2 :=null;
        child_3 :=null;
        child_4 :=null;
        child_5 :=null;
        keynum := 0;
        key_1 := 0;
        key_2 := 0;
        key_3 := 0;
        key_4 := 0;
        key_5 := 0;
        Contents := {};
        Repr := {this};
    }

}