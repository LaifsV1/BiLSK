require "substitution.k"

module BILS-SYNTAX
  imports DOMAINS-SYNTAX
  imports SUBSTITUTION

  // TODO:
  // - unexplainable bug with associativity of sequencing
  //   i.e. fun f -> f 6 ; ( ref l2 = 2 in f ! l2 )
  //   why does ; need brackets on the second term?
  syntax Exp ::= KVar | Val | EVal
               | "!" KVar
               > Exp Exp                          [seqstrict(1,2), left]
               > "not" Exp                        [strict(1)]
               > Exp "*" Exp                      [seqstrict(1,2), left]
               | Exp "/" Exp                      [seqstrict(1,2), left]
               > Exp "+" Exp                      [seqstrict(1,2), left]
               | Exp "-" Exp                      [seqstrict(1,2), left]
               > Exp "<" Exp                      [seqstrict(1,2), left]
               | Exp ">" Exp                      [seqstrict(1,2), left]
               | Exp "<=" Exp                     [seqstrict(1,2), left]
               | Exp ">=" Exp                     [seqstrict(1,2), left]
               | Exp "==" Exp                     [seqstrict(1,2), left]
               > Exp "and" Exp                    [seqstrict(1,2), left]
               > Exp "or" Exp                     [seqstrict(1,2), left]
               > KVar ":=" Exp                    [strict(2), right]
               > "if" Exp "then" Exp "else" Exp   [strict(1)]
               > Exp ";" Exp                      [strict(1), right, seq]
               > "let" KVar "=" Exp "in" Exp      [binder, strict(2)]
               | "let rec" KVar "=" Exp "in" Exp  [binder, strict(2)]
               | "ref" KVar "=" Exp "in" Exp      [binder, strict(2)]
               | "(" Exp ")"                      [bracket]
  syntax Prog ::= Exp "|||" Exp
                | "#bound" Int Exp "|||" Exp 
  syntax Val ::= Const | "fun" KVar "->" Exp [binder,fun]
  syntax Const ::= Int | Bool | "()"
  syntax EVal ::= Bot | Nil
  syntax Bot ::= "_bot_" // bottom is just fail
  syntax Nil ::= "_nil_"
  syntax priorities seq > fun
endmodule

module BILS
  imports BILS-SYNTAX
  imports SUBSTITUTION
  imports COLLECTIONS
  imports DOMAINS
  imports SET

  syntax KResult ::= Val
  syntax Prog ::= Exp

  syntax Label ::= "ocall" Int Val | "oret" Val
                 | "pcall" KVar Val | "pret" Val
                 | "!DIV!"

  syntax Mode ::= "_NORMAL_" | "_DIVERGE_" | "_ERROR_"

  configuration 
      <T>
        <bisim>
          <mode> _NORMAL_ </mode>
          <expr multiplicity="*">
            <id> 0 </id>
            <k> $PGM:Prog </k>
            <state> .Map </state>
            <eval> .K </eval>
            <pub> .Map </pub>
            <trace> .K </trace>
            <step> 10 </step>
          </expr>
          <R> //TODO: is explored sufficient? do you need 1 and 2?
            <C multiplicity="*">
              //first term
              <s1> .Map </s1>
              <e1> .K </e1>
              <g1> .Map </g1>
              //second term
              <s2> .Map </s2>
              <e2> .K </e2>
              <g2> .Map </g2>
            </C>
          </R>
        </bisim>
      </T>

  //=====================
  // INITIALISATION STEP:
  //==bound-specified==
  rule <expr>
         ...
         <id> _ => 1 </id>
         <k> #bound I:Int E1 ||| E2 => E1 </k>
         <step> _ => I </step>
         ...
       </expr>
       (.Bag => <expr>
                  ...
                  <id> 2 </id>
                  <k> E2 </k>
                  <step> I </step>
                  ...
                </expr>)
  //==bound-not-specified==
  rule <expr>...<id> _ => 1 </id><k> E1 ||| E2 => E1 </k>...</expr>
       (.Bag => <expr>...<id> 2 </id><k> E2 </k>...</expr>)

  //================================
  // CONCRETE OPERATIONAL SEMANTICS:
  //TODO: check bounds!!!
  //TODO: add type annotation to lambda
  //==divergence==
  rule EV:EVal ~> K:KItem => EV
  //==arithmetic==
  rule I1:Int +  I2:Int => I1 +Int  I2
  rule I1:Int -  I2:Int => I1 -Int  I2
  rule I1:Int *  I2:Int => I1 *Int  I2
  rule I1:Int /  I2:Int => I1 /Int  I2
  rule I1:Int >  I2:Int => I1 >Int  I2
  rule I1:Int <  I2:Int => I1 <Int  I2
  rule I1:Int >= I2:Int => I1 >=Int I2
  rule I1:Int <= I2:Int => I1 <=Int I2
  rule I1:Int == I2:Int => I1 ==Int I2
  rule B1:Bool ==  B2:Bool => B1 ==Bool  B2
  rule B1:Bool and B2:Bool => B1 andBool B2
  rule B1:Bool or  B2:Bool => B1 orBool  B2
  rule not B:Bool => notBool B
  //==conditionals==
  rule if true  then ET else EF => ET
  rule if false then ET else EF => EF
  //==application-success==
  rule <expr>
       ...
       <k> (fun X:KVar -> E:Exp) V:Val => E[V/X] ... </k>
       <step> I => I -Int 1 </step>
       ...
       </expr>
       requires I >Int 0
  //==application-nil==
  rule <expr>
       ...
       <k> (fun X:KVar -> E:Exp) V:Val => _nil_ ... </k>
       <step> I </step>
       ...
       </expr>
       requires I <=Int 0
  //==new-location==
  rule <expr>
       ...
       <k> ref L:KVar = V:Val in E:Exp => E[!L2/L] ... </k>
       <state> ... .Map => (!L2:KVar |-> V) ... </state>
       ...
       </expr>
  //==dereferencing==
  rule <expr>
       ...
       <k> ! L:KVar => V ... </k>
       <state> ... (L |-> V) ... </state>
       ...
       </expr>
  //==assignment==
  rule <expr>
       ...
       <k> L:KVar := V:Val => ():Const ... </k>
       <state> ... L |-> (_ => V) ... </state>
       ...
       </expr>
  //==sequencing==
  rule V:Val ; E:Exp => E
  //==let-binding==
  rule let X:KVar = V:Val in E:Exp => E[V/X]
  //==let-rec-binding==
  rule let rec F:KVar = V:Val in E:Exp
       =>
       E[V[let rec F = V in F/F]/F]

  //====================
  // LTS-GAME SEMANTICS:
  syntax Prog ::= "!OPPONENT!"
  syntax AbsVal ::= "!abs!" KVar
  syntax Const  ::= AbsVal
  //==PROPONENT-ANSWERS==
  //==proponent-answer-constant==
  rule <mode> _NORMAL_ </mode>
       <expr>
         ...
         <id> 1 </id>
         <k> C:Const => !OPPONENT! </k>
         <state> ST1 </state>
         <eval> ES1 </eval>
         <pub> P1 </pub>
         <trace> TR1 => TR1 ~> pret C </trace>
         ...
       </expr>
       <expr>
         ...
         <id> 2 </id>
         <k> C:Const => !OPPONENT! </k>
         <state> ST2 </state>
         <eval> ES2 </eval>
         <pub> P2 </pub>
         <trace> TR2 => TR2 ~> pret C </trace>
         ...
       </expr>
       <R>
         ...
         (.Bag
           =>
           <C>
             //first term
             <s1> ST1 </s1>
             <e1> ES1 </e1>
             <g1> P1 </g1>
             //second term
             <s2> ST2 </s2>
             <e2> ES2 </e2>
             <g2> P2 </g2>
           </C>)
         ...
       </R>
  //==proponent-answer-lambda==
  rule <mode> _NORMAL_ </mode>
       <expr>
         ...
         <id> 1 </id>
         <k> fun X:KVar -> EX:Exp  => !OPPONENT! </k>
         <pub> P1 => P1[!I:Int <- (fun X -> EX)] </pub>
         <state> ST1 </state>
         <eval> ES1 </eval>
         <trace> TR1 => TR1 ~> pret (fun X -> EX) </trace>
         ...
       </expr>
       <expr>
         ...
         <id> 2 </id>
         <k> fun Y:KVar -> EY:Exp  => !OPPONENT! </k>
         <pub> P2 => P2[!I <- (fun Y -> EY)] </pub>
         <state> ST2 </state>
         <eval> ES2 </eval>
         <trace> TR2 => TR2 ~> pret (fun Y -> EY) </trace>
         ...
       </expr>
       <R>
         ...
         (.Bag
           =>
           <C>
             //first term
             <s1> ST1 </s1>
             <e1> ES1 </e1>
             <g1> P1[!I <- (fun X -> EX)] </g1>
             //second term
             <s2> ST2 </s2>
             <e2> ES2 </e2>
             <g2> P2[!I <- (fun Y -> EY)] </g2>
           </C>)
         ...
       </R>
       
  //==PROPONENT-QUESTIONS==
  //==proponent-question-const==
  rule <mode> _NORMAL_ </mode>
       <expr>
         ...
         <id> 1 </id>
         <k> (!abs! F) C:Const ~> E1 => !OPPONENT! </k>
         <pub> P1 </pub>
         <state> ST1 </state>
         <eval> ES1 => E1 ~> (!abs! F) ~> ES1 </eval>
         <trace> TR1 => TR1 ~> pcall F C </trace>
         ...
       </expr>
       <expr>
         ...
         <id> 2 </id>
         <k> (!abs! F) C:Const ~> E2 => !OPPONENT! </k>
         <pub> P2 </pub>
         <state> ST2 </state>
         <eval> ES2 => E2 ~> (!abs! F) ~> ES2 </eval>
         <trace> TR2 => TR2 ~> pcall F C </trace>
         ...
       </expr>
       <R>
         ...
         (.Bag
           =>
           <C>
             //first term
             <s1> ST1 </s1>
             <e1> E1 ~> (!abs! F) ~> ES1 </e1>
             <g1> P1 </g1>
             //second term
             <s2> ST2 </s2>
             <e2> E2 ~> (!abs! F) ~> ES2 </e2>
             <g2> P2 </g2>
           </C>)
         ...
       </R>
  //==proponent-question-lambda==
  rule <mode> _NORMAL_ </mode>
       <expr>
         ...
         <id> 1 </id>
         <k>
           (!abs! F) (fun X:KVar -> EX:Exp) ~> E1
           =>
           !OPPONENT!
         </k>
         <pub> P1 => P1[!I:Int <- (fun X -> EX)] </pub>
         <state> ST1 </state>
         <eval> ES1 => E1 ~> (!abs! F) ~> ES1 </eval>
         <trace> TR1 => TR1 ~> pcall F (fun X -> EX) </trace>
         ...
       </expr>
       <expr>
         ...
         <id> 2 </id>
         <k>
           (!abs! F) (fun Y:KVar -> EY:Exp) ~> E2
           =>
           !OPPONENT!
         </k>
         <pub> P2 => P2[!I <- (fun Y -> EY)] </pub>
         <state> ST2 </state>
         <eval> ES2 => E2 ~> (!abs! F) ~> ES2 </eval>
         <trace> TR2 => TR2 ~> pcall F (fun Y -> EY) </trace>
         ...
       </expr>
       <R>
         ...
         (.Bag
           =>
           <C>
             //first term
             <s1> ST1 </s1>
             <e1> E1 ~> (!abs! F) ~> ES1 </e1>
             <g1> P1[!I:Int <- (fun X -> EX)] </g1>
             //second term
             <s2> ST2 </s2>
             <e2> E2 ~> (!abs! F) ~> ES2 </e2>
             <g2> P2[!I <- (fun Y -> EY)] </g2>
           </C>)
         ...
       </R>
  //==OPPONENT-ANSWERS==
  // TODO: maybe use only Boolean constants.
  //==opponent-answer-true==
  rule <mode> _NORMAL_ </mode>
       <expr>
         ...
         <id> 1 </id>
         <k> !OPPONENT! => true ~> E1 </k>
         <eval> E1:KItem ~> (!abs! N) ~> ES1 => ES1 </eval>
         <trace> TR1 => TR1 ~> oret true </trace>
         <step> S </step>
         ...
       </expr>
       <expr>
         ...
         <id> 2 </id>
         <k> !OPPONENT! => true ~> E2 </k>
         <eval> E2:KItem ~> (!abs! N) ~> ES2 => ES2 </eval>
         <trace> TR2 => TR2 ~> oret true </trace>
         <step> S </step>
         ...
       </expr>
       requires S >Int 0
       [transition]
  //==opponent-answer-false==
  rule <mode> _NORMAL_ </mode>
       <expr>
         ...
         <id> 1 </id>
         <k> !OPPONENT! => false ~> E1 </k>
         <eval> E1:KItem ~> (!abs! N) ~> ES1 => ES1 </eval>
         <trace> TR1 => TR1 ~> oret false </trace>
         <step> S </step>
         ...
       </expr>
       <expr>
         ...
         <id> 2 </id>
         <k> !OPPONENT! => false ~> E2 </k>
         <eval> E2:KItem ~> (!abs! N) ~> ES2 => ES2 </eval>
         <trace> TR2 => TR2 ~> oret false </trace>
         <step> S </step>
         ...
       </expr>
       requires S >Int 0
       [transition]
  //==opponent-answer-lambda==
  rule <mode> _NORMAL_ </mode>
       <expr>
         ...
         <id> 1 </id>
         <k>
           !OPPONENT!
           =>
           (fun !X:KVar -> (!abs! !Y:KVar) !X) ~> E1
         </k>
         <eval> E1:KItem ~> (!abs! N) ~> ES1 => ES1 </eval>
         <trace> TR1 => TR1 ~> oret (fun !X -> (!abs! !Y) !X) </trace>
         <step> S </step>
         ...
       </expr>
       <expr>
         ...
         <id> 2 </id>
         <k>
           !OPPONENT!
           =>
           (fun !X -> (!abs! !Y) !X) ~> E2
         </k>
         <eval> E2:KItem ~> (!abs! N) ~> ES2 => ES2 </eval>
         <trace> TR2 => TR2 ~> oret (fun !X -> (!abs! !Y) !X) </trace>
         <step> S </step>
         ...
       </expr>
       requires S >Int 0
       [transition]
  //==OPPONENT-QUESTIONS==
  //==opponent-question-true==
  rule <mode> _NORMAL_ </mode>
       <expr>
         ...
         <id> 1 </id>
         <k> !OPPONENT! => EX1[true/X1] </k>
         <pub> ... I |-> (fun X1 -> EX1) ... </pub>
         <trace> TR1 => TR1 ~> ocall I true </trace>
         <step> S => S -Int 1 </step>
         ...
       </expr>
       <expr>
         ...
         <id> 2 </id>
         <k> !OPPONENT! => EX2[true/X2] </k>
         <pub> ... I |-> (fun X2 -> EX2) ... </pub>
         <trace> TR2 => TR2 ~> ocall I true </trace>
         <step> S => S -Int 1 </step>
         ...
       </expr>
       requires S >Int 0
       [transition]
  //==opponent-question-false==
  rule <mode> _NORMAL_ </mode>
       <expr>
         ...
         <id> 1 </id>
         <k> !OPPONENT! => EX1[false/X1] </k>
         <pub> ... I |-> (fun X1 -> EX1) ... </pub>
         <trace> TR1 => TR1 ~> ocall I false </trace>
         <step> S => S -Int 1 </step>
         ...
       </expr>
       <expr>
         ...
         <id> 2 </id>
         <k> !OPPONENT! => EX2[false/X2] </k>
         <pub> ... I |-> (fun X2 -> EX2) ... </pub>
         <trace> TR2 => TR2 ~> ocall I false </trace>
         <step> S => S -Int 1 </step>
         ...
       </expr>
       requires S >Int 0
       [transition]
  //==opponent-question-lambda==
  rule <mode> _NORMAL_ </mode>
       <expr>
         ...
         <id> 1 </id>
         <k>
           !OPPONENT!
           =>
           EX1[(fun !Y:KVar -> (!abs! !F:KVar) !Y)/X1]
         </k>
         <pub> ... I |-> (fun X1 -> EX1) ... </pub>
         <trace>
           TR1 => TR1 ~> ocall I (fun !Y -> (!abs! !F) !Y) </trace>
         <step> S => S -Int 1 </step>
         ...
       </expr>
       <expr>
         ...
         <id> 2 </id>
         <k>
           !OPPONENT!
           =>
           EX2[(fun !Y -> (!abs! !F) !Y)/X2]
         </k>
         <pub> ... I |-> (fun X2 -> EX2) ... </pub>
         <trace>
           TR2 => TR2 ~> ocall I (fun !Y -> (!abs! !F) !Y) </trace>
         <step> S => S -Int 1 </step>
         ...
       </expr>
       requires S >=Int 0
       [transition]

  //==GAME-REACHES-NIL==
  //==either-opponent-nil==
  rule <expr>
         ...
         <k> !OPPONENT! => _nil_ </k>
         <step> S </step>
         ...
       </expr>
       requires S <=Int 0

  //====================================
  // RULES TO SWITCH TO DIVERGENCE MODE:
  //==PROPONENT-ANSWERS==
  //==proponent-answer-const-neq==
  syntax Label ::= "!UNMATCHED!" "(" Label ")"
  rule <mode> _NORMAL_ => _DIVERGE_ </mode>
       <expr>
         ...
         <k> C1:Const => !OPPONENT! </k>
         <trace> TR1 => TR1 ~> !UNMATCHED!( pret C1 ) </trace>
         ...
       </expr>
       <expr>
         ...
         <k> C2:Const => !OPPONENT! </k>
         <trace> TR2 => TR2 ~> !UNMATCHED!( pret C2 ) </trace>
         ...
       </expr>
       requires C1 =/=K C2
  //==proponent-answer-lambda-neq==: not needed.
  //==proponent-answer-const-lambda==
  rule <mode> _NORMAL_ => _DIVERGE_ </mode>
       <expr>
         ...
         <k> C1:Const => !OPPONENT! </k>
         <trace> TR1 => TR1 ~> pret C1 ~> !DIV! </trace>
         ...
       </expr>
       <expr>
         ...
         <k> fun X:KVar -> EX:Exp  => !OPPONENT! </k>
         <pub> ... .Map => (!I:Int |-> (fun X -> EX)) ... </pub>
         <trace> TR1 => TR1 ~> pret (fun X -> EX) ~> !DIV! </trace>
         ...
       </expr>

  //==PROPONENT-QUESTIONS==
  //==proponent-question-const-neq==
  rule <mode> _NORMAL_ => _DIVERGE_ </mode>
       <expr>
         ...
         <id> 1 </id>
         <k> (!abs! X) C1:Const ~> E1 => !OPPONENT! </k>
         <eval> ES1 => E1 ~> (!abs! X) ~> ES1 </eval>
         <trace> TR1 => TR1 ~> pcall X C1 ~> !DIV! </trace>
         ...
       </expr>
       <expr>
         ...
         <id> 2 </id>
         <k> (!abs! Y) C2:Const ~> E2 => !OPPONENT! </k>
         <eval> ES2 => E2 ~> (!abs! Y) ~> ES2 </eval>
         <trace> TR2 => TR2 ~> pcall Y C2 ~> !DIV! </trace>
         ...
       </expr>
       requires (X =/=K Y) orBool (C1 =/=K C2)
  //==proponent-question-lambda==
  rule <mode> _NORMAL_ => _DIVERGE_ </mode>
       <expr>
         ...
         <id> 1 </id>
         <k>
           (!abs! F1) (fun X:KVar -> EX:Exp) ~> E1
           =>
           !OPPONENT!
         </k>
         <pub> ... .Map => (!I:Int |-> (fun X -> EX)) ... </pub>
         <eval> ES1 => E1 ~> (!abs! F1) ~> ES1 </eval>
         <trace> TR1 => TR1 ~> pcall F1 (fun X -> EX) ~> !DIV! </trace>
         ...
       </expr>
       <expr>
         ...
         <id> 2 </id>
         <k>
           (!abs! F2) (fun Y:KVar -> EY:Exp) ~> E2
           =>
           !OPPONENT!
         </k>
         <pub> ... .Map => (!I:Int |-> (fun Y -> EY)) ... </pub>
         <eval> ES2 => E2 ~> (!abs! F2) ~> ES2 </eval>
         <trace> TR2 => TR2 ~> pcall F2 (fun Y -> EY) ~> !DIV! </trace>
         ...
       </expr>
       requires F1 =/=K F2
  //==proponent-question-const-lambda==
  rule <mode> _NORMAL_ => _DIVERGE_ </mode>
       <expr>
         ...
         <k> (!abs! F1) C1:Const ~> E1 => !OPPONENT! </k>
         <eval> ES1 => E1 ~> (!abs! F1) ~> ES1 </eval>
         <trace> TR1 => TR1 ~> pcall F1 C1 ~> !DIV! </trace>
         ...
       </expr>
       <expr>
         ...
         <k>
           (!abs! F2) (fun Y:KVar -> EY:Exp) ~> E2
           =>
           !OPPONENT!
         </k>
         <pub> ... .Map => (!I:Int |-> (fun Y -> EY)) ... </pub>
         <eval> ES2 => E2 ~> (!abs! F2) ~> ES2 </eval>
         <trace> TR2 => TR2 ~> pcall F2 (fun Y -> EY) ~> !DIV! </trace>
         ...
       </expr>

  //==PROPONENT-ANSWERS-QUESTIONS==
  // combinatorial combination of CALL and RET rules.
  // i.e. 2 answer and 2 question rules = 4 combined rules.

  //==proponent-answer-constant-question-constant==
  rule <mode> _NORMAL_ => _DIVERGE_ </mode>
       <expr>
         ...
         <k> C:Const => !OPPONENT! </k>
         <trace> TR1 => TR1 ~> pret C ~> !DIV! </trace>
         ...
       </expr>
       <expr>
         ...
         <k> (!abs! F) C:Const ~> E2 => !OPPONENT! </k>
         <eval> ES2 => E2 ~> (!abs! F) ~> ES2 </eval>
         <trace> TR2 => TR2 ~> pcall F C ~> !DIV! </trace>
         ...
       </expr>
  //==proponent-answer-lambda-question-constant==
  rule <mode> _NORMAL_ => _DIVERGE_ </mode>
       <expr>
         ...
         <k> fun X:KVar -> EX:Exp  => !OPPONENT! </k>
         <pub> ... .Map => (!I:Int |-> (fun X -> EX)) ... </pub>
         <trace> TR1 => TR1 ~> pret (fun X -> EX) ~> !DIV! </trace>
         ...
       </expr>
       <expr>
         ...
         <k> (!abs! F) C:Const ~> E2 => !OPPONENT! </k>
         <eval> ES2 => E2 ~> (!abs! F) ~> ES2 </eval>
         <trace> TR2 => TR2 ~> pcall F C ~> !DIV! </trace>
         ...
       </expr>
  //==proponent-answer-constant-question-lambda==
  rule <mode> _NORMAL_ => _DIVERGE_ </mode>
       <expr>
         ...
         <k> C:Const => !OPPONENT! </k>
         <trace> TR1 => TR1 ~> pret C ~> !DIV! </trace>
         ...
       </expr>
       <expr>
         ...
         <k>
           (!abs! F) (fun Y:KVar -> EY:Exp) ~> E2
           =>
           !OPPONENT!
         </k>
         <pub> ... .Map => (!I:Int |-> (fun Y -> EY)) ... </pub>
         <eval> ES2 => E2 ~> (!abs! F) ~> ES2 </eval>
         <trace> TR2 => TR2 ~> pcall F (fun Y -> EY) ~> !DIV! </trace>
         ...
       </expr>
  //==proponent-answer-lambda==
  rule <mode> _NORMAL_ => _DIVERGE_ </mode>
       <expr>
         ...
         <k> fun X:KVar -> EX:Exp  => !OPPONENT! </k>
         <pub> ... .Map => (!I:Int |-> (fun X -> EX)) ... </pub>
         <trace> TR1 => TR1 ~> pret (fun X -> EX) ~> !DIV! </trace>
         ...
       </expr>
       <expr>
         ...
         <k>
           (!abs! F) (fun Y:KVar -> EY:Exp) ~> E2
           =>
           !OPPONENT!
         </k>
         <pub> ... .Map => (!I:Int |-> (fun Y -> EY)) ... </pub>
         <eval> ES2 => E2 ~> (!abs! F) ~> ES2 </eval>
         <trace> TR2 => TR2 ~> pcall F (fun Y -> EY) ~> !DIV! </trace>
         ...
       </expr>

  // CANT DIVERGE ON OPPONENT SO NO OPPONENT MOVES...

  //=======================
  // DIVERGENCE MODE RULES:
  // we execute the first term first.
  // we try to reach nil or an error.
  //---------------------------------
  // ID 1
  //==DIVERGE-PROPONENT-ANSWERS==
  //==proponent-answer-constant==
  rule <mode> _DIVERGE_ </mode>
       <expr>
         ...
         <id> 1 </id>
         <k> C:Const => !OPPONENT! </k>
         <trace> TR1 => TR1 ~> pret C </trace>
         ...
       </expr>
  //==proponent-answer-lambda==
  rule <mode> _DIVERGE_ </mode>
       <expr>
         ...
         <id> 1 </id>
         <k> fun X:KVar -> EX:Exp  => !OPPONENT! </k>
         <pub> ... .Map => (!I:Int |-> (fun X -> EX)) ... </pub>
         <trace> TR1 => TR1 ~> pret (fun X -> EX) </trace>
         ...
       </expr>
  //==DIVERGE-PROPONENT-QUESTIONS==
  //==proponent-question-const==
  rule <mode> _DIVERGE_ </mode>
       <expr>
         ...
         <id> 1 </id>
         <k> (!abs! F) C:Const ~> E1 => !OPPONENT! </k>
         <eval> ES1 => E1 ~> (!abs! F) ~> ES1 </eval>
         <trace> TR1 => TR1 ~> pcall F C </trace>
         ...
       </expr>
  //==proponent-question-lambda==
  rule <mode> _DIVERGE_ </mode>
       <expr>
         ...
         <id> 1 </id>
         <k>
           (!abs! F) (fun X:KVar -> EX:Exp) ~> E1
           =>
           !OPPONENT!
         </k>
         <pub> ... .Map => (!I:Int |-> (fun X -> EX)) ... </pub>
         <eval> ES1 => E1 ~> (!abs! F) ~> ES1 </eval>
         <trace> TR1 => TR1 ~> pcall F (fun X -> EX) </trace>
         ...
       </expr>
  //==DIVERGE-OPPONENT-ANSWERS==
  //==opponent-answer-true==
  rule <mode> _DIVERGE_ </mode>
       <expr>
         ...
         <id> 1 </id>
         <k> !OPPONENT! => true ~> E1 </k>
         <eval> E1:KItem ~> (!abs! F) ~> ES1 => ES1 </eval>
         <trace> TR1 => TR1 ~> oret true </trace>
         <step> S </step>
         ...
       </expr>
       requires (S >Int 0)
       [transition]
  //==opponent-answer-false==
  rule <mode> _DIVERGE_ </mode>
       <expr>
         ...
         <id> 1 </id>
         <k> !OPPONENT! => false ~> E1 </k>
         <eval> E1:KItem ~> (!abs! F) ~> ES1 => ES1 </eval>
         <trace> TR1 => TR1 ~> oret false </trace>
         <step> S </step>
         ...
       </expr>
       requires (S >Int 0)
       [transition]
  //==opponent-answer-lambda==
  rule <mode> _DIVERGE_ </mode>
       <expr>
         ...
         <id> 1 </id>
         <k>
           !OPPONENT!
           =>
           (fun !X:KVar -> (!abs! !Y:KVar) !X) ~> E1
         </k>
         <eval> E1:KItem ~> (!abs! F) ~> ES1 => ES1 </eval>
         <trace> TR1 => TR1 ~> oret (fun !X -> (!abs! !Y) !X) </trace>
         <step> S </step>
         ...
       </expr>
       requires (S >Int 0)
       [transition]
  //==DIVERGE-OPPONENT-QUESTIONS==
  //==opponent-question-true==
  rule <mode> _DIVERGE_ </mode>
       <expr>
         ...
         <id> 1 </id>
         <k> !OPPONENT! => EX1[true/X1] </k>
         <pub> ... I |-> (fun X1 -> EX1) ... </pub>
         <trace> TR1 => TR1 ~> ocall I true </trace>
         <step> S => S -Int 1 </step>
         ...
       </expr>
       requires (S >Int 0)
       [transition]
  //==opponent-question-false==
  rule <mode> _DIVERGE_ </mode>
       <expr>
         ...
         <id> 1 </id>
         <k> !OPPONENT! => EX1[false/X1] </k>
         <pub> ... I |-> (fun X1 -> EX1) ... </pub>
         <trace> TR1 => TR1 ~> ocall I false </trace>
         <step> S => S -Int 1 </step>
         ...
       </expr>
       requires (S >Int 0)
       [transition]
  //==proponent-question-lambda==
  rule <mode> _DIVERGE_ </mode>
       <expr>
         ...
         <id> 1 </id>
         <k>
           !OPPONENT!
           =>
           EX1[(fun !Y:KVar -> (!abs! !F:KVar) !Y)/X1]
         </k>
         <pub> ... I |-> (fun X1 -> EX1) ... </pub>
         <trace>
           TR1 => TR1 ~> ocall I (fun !Y -> (!abs! !F) !Y) </trace>
         <step> S => S -Int 1 </step>
         ...
       </expr>
       requires (S >Int 0)
       [transition]

  //-------------
  // ID 2
  //=====
  //==DIVERGE-PROPONENT-ANSWERS==
  //==proponent-answer-constant==
  rule <mode> _DIVERGE_ </mode>
       <expr>...<id> 1 </id><k> _nil_ </k>...</expr>
       <expr>
         ...
         <id> 2 </id>
         <k> C:Const => !OPPONENT! </k>
         <trace> TR1 => TR1 ~> pret C </trace>
         ...
       </expr>
  //==proponent-answer-lambda==
  rule <mode> _DIVERGE_ </mode>
       <expr>...<id> 1 </id><k> _nil_ </k>...</expr>
       <expr>
         ...
         <id> 2 </id>
         <k> fun X:KVar -> EX:Exp  => !OPPONENT! </k>
         <pub> ... .Map => (!I:Int |-> (fun X -> EX)) ... </pub>
         <trace> TR1 => TR1 ~> pret (fun X -> EX) </trace>
         ...
       </expr>
  //==DIVERGE-PROPONENT-QUESTIONS==
  //==proponent-question-const==
  rule <mode> _DIVERGE_ </mode>
       <expr>...<id> 1 </id><k> _nil_ </k>...</expr>
       <expr>
         ...
         <id> 2 </id>
         <k> (!abs! F) C:Const ~> E1 => !OPPONENT! </k>
         <eval> ES1 => E1 ~> (!abs! F) ~> ES1 </eval>
         <trace> TR1 => TR1 ~> pcall F C </trace>
         ...
       </expr>
  //==proponent-question-lambda==
  rule <mode> _DIVERGE_ </mode>
       <expr>...<id> 1 </id><k> _nil_ </k>...</expr>
       <expr>
         ...
         <id> 2 </id>
         <k>
           (!abs! F) (fun X:KVar -> EX:Exp) ~> E1
           =>
           !OPPONENT!
         </k>
         <pub> ... .Map => (!I:Int |-> (fun X -> EX)) ... </pub>
         <eval> ES1 => E1 ~> (!abs! F) ~> ES1 </eval>
         <trace> TR1 => TR1 ~> pcall F (fun X -> EX) </trace>
         ...
       </expr>
  //==DIVERGE-OPPONENT-ANSWERS==
  //==opponent-answer-true==
  rule <mode> _DIVERGE_ </mode>
       <expr>...<id> 1 </id><k> _nil_ </k>...</expr>
       <expr>
         ...
         <id> 2 </id>
         <k> !OPPONENT! => true ~> E1 </k>
         <eval> E1:KItem ~> (!abs! F) ~> ES1 => ES1 </eval>
         <trace> TR1 => TR1 ~> oret true </trace>
         <step> S </step>
         ...
       </expr>
       requires (S >Int 0)
       [transition]
  //==opponent-answer-false==
  rule <mode> _DIVERGE_ </mode>
       <expr>...<id> 1 </id><k> _nil_ </k>...</expr>
       <expr>
         ...
         <id> 2 </id>
         <k> !OPPONENT! => false ~> E1 </k>
         <eval> E1:KItem ~> (!abs! F) ~> ES1 => ES1 </eval>
         <trace> TR1 => TR1 ~> oret false </trace>
         <step> S </step>
         ...
       </expr>
       requires (S >Int 0)
       [transition]
  //==opponent-answer-lambda==
  rule <mode> _DIVERGE_ </mode>
       <expr>...<id> 1 </id><k> _nil_ </k>...</expr>
       <expr>
         ...
         <id> 2 </id>
         <k>
           !OPPONENT!
           =>
           (fun !X:KVar -> (!abs! !Y:KVar) !X) ~> E1
         </k>
         <eval> E1:KItem ~> (!abs! F) ~> ES1 => ES1 </eval>
         <trace> TR1 => TR1 ~> oret (fun !X -> (!abs! !Y) !X) </trace>
         <step> S </step>
         ...
       </expr>
       requires (S >Int 0)
       [transition]
  //==DIVERGE-OPPONENT-QUESTIONS==
  //==opponent-question-true==
  rule <mode> _DIVERGE_ </mode>
       <expr>...<id> 1 </id><k> _nil_ </k>...</expr>
       <expr>
         ...
         <id> 2 </id>
         <k> !OPPONENT! => EX1[true/X1] </k>
         <pub> ... I |-> (fun X1 -> EX1) ... </pub>
         <trace> TR1 => TR1 ~> ocall I true </trace>
         <step> S => S -Int 1 </step>
         ...
       </expr>
       requires (S >Int 0)
       [transition]
  //==opponent-question-false==
  rule <mode> _DIVERGE_ </mode>
       <expr>...<id> 1 </id><k> _nil_ </k>...</expr>
       <expr>
         ...
         <id> 2 </id>
         <k> !OPPONENT! => EX1[false/X1] </k>
         <pub> ... I |-> (fun X1 -> EX1) ... </pub>
         <trace> TR1 => TR1 ~> ocall I false </trace>
         <step> S => S -Int 1 </step>
         ...
       </expr>
       requires (S >Int 0)
       [transition]
  //==proponent-question-lambda==
  rule <mode> _DIVERGE_ </mode>
       <expr>...<id> 1 </id><k> _nil_ </k>...</expr>
       <expr>
         ...
         <id> 2 </id>
         <k>
           !OPPONENT!
           =>
           EX1[(fun !Y:KVar -> (!abs! !F:KVar) !Y)/X1]
         </k>
         <pub> ... I |-> (fun X1 -> EX1) ... </pub>
         <trace>
           TR1 => TR1 ~> ocall I (fun !Y -> (!abs! !F) !Y) </trace>
         <step> S => S -Int 1 </step>
         ...
       </expr>
       requires (S >Int 0)
       [transition]

  //============
  // ERROR MODE:
  // checks if one side can reach empty stack at oppponent
  // while the other side is at nil
  syntax Label ::= "!TERM!"
  rule <mode> _DIVERGE_ => _ERROR_ </mode>
       <expr>
         ...
         <k> !OPPONENT! </k>
         <eval> .K </eval>
         <trace> TR => TR ~> !TERM! </trace>
         ...
       </expr>
       [transition]
endmodule