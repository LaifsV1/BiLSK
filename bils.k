require "substitution.k"

module BILS-SYNTAX
  imports DOMAINS-SYNTAX
  imports SUBSTITUTION

  syntax Exp ::= KVar | Val | EVal
               | "!" KVar
               > Exp Exp                              [seqstrict(1,2), left]
               > "not" Exp                            [strict(1)]
               > Exp "*" Exp                          [seqstrict(1,2), left]
               | Exp "/" Exp                          [seqstrict(1,2), left]
               > Exp "+" Exp                          [seqstrict(1,2), left]
               | Exp "-" Exp                          [seqstrict(1,2), left]
               > Exp "<" Exp                          [seqstrict(1,2), left]
               | Exp ">" Exp                          [seqstrict(1,2), left]
               | Exp "<=" Exp                         [seqstrict(1,2), left]
               | Exp ">=" Exp                         [seqstrict(1,2), left]
               | Exp "==" Exp                         [seqstrict(1,2), left]
               > Exp "and" Exp                        [seqstrict(1,2), left]
               > Exp "or" Exp                         [seqstrict(1,2), left]
               > KVar ":=" Exp                        [strict(2), right]
               > "if" Exp "then" Exp "else" Exp       [strict(1)]
               > Exp ";" Exp                          [strict(1), right, seq]
               > "let" KVar "=" Exp "in" Exp          [binder, strict(2)]
               | "let rec" KVar "=" Exp "in" Exp      [binder, strict(2)]
               | "ref" KVar "=" Exp "in" Exp          [binder, strict(2)]
               | "fun" KVar "->" Exp                  [binder]
               | "(" Exp ")"                          [bracket]
  syntax Prog ::= Exp "||" Exp
                | "#bound" Int Exp "||" Exp 
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

  //TODO: config organisation. What can go outside <bisim>?
  //TODO: could I have the step counter cover both terms?
  configuration 
      <T>
        <bisim>        
          <expr multiplicity="*">
            <k> $PGM:Prog </k>
            <state> .Map </state>
            <eval> .K </eval>
            <pub> .Map </pub>
            <trace> .K </trace>
            <step> 10 </step>
          </expr>
        </bisim>
      </T>

  //====================
  // INITIALISATION STEP
  //==bound-specified==
  rule <expr>
         ...
         <k> #bound I:Int E1 || E2 => E1 </k>
         <step> _ => I </step>
         ...
       </expr>
       (.Bag => <expr>...<k> E2 </k><step> I </step>...</expr>)
  //==bound-not-specified==
  rule <expr>...<k> E1 || E2 => E1 </k>...</expr>
       (.Bag => <expr>...<k> E2 </k>...</expr>)

  //================================
  // CONCRETE OPERATIONAL SEMANTICS:
  //TODO: check bounds!!!
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
       <k> (fun X:KVar -> E:Exp) V:Val => _nil_ </k>
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
  rule <expr>
         ...
         <k> C:Const => !OPPONENT! </k>
         <trace> TR1 => TR1 ~> pret C </trace>
         <step> S </step>
         ...
       </expr>
       <expr>
         ...
         <k> C:Const => !OPPONENT! </k>
         <trace> TR2 => TR2 ~> pret C </trace>
         <step> S </step>
         ...
       </expr>
       requires S >Int 0
       [transition]
  //==proponent-answer-lambda==
  rule <expr>
         ...
         <k> fun X:KVar -> EX:Exp  => !OPPONENT! </k>
         <pub> ... .Map => (!I:Int |-> (fun X -> EX)) ... </pub>
         <trace> TR1 => TR1 ~> pret (fun X -> EX) </trace>
         <step> S </step>
         ...
       </expr>
       <expr>
         ...
         <k> fun Y:KVar -> EY:Exp  => !OPPONENT! </k>
         <pub> ... .Map => (!I:Int |-> (fun Y -> EY)) ... </pub>
         <trace> TR2 => TR2 ~> pret (fun Y -> EY) </trace>
         <step> S </step>
         ...
       </expr>
       requires S >Int 0
       [transition]
       
  //==PROPONENT-QUESTIONS==
  //==proponent-question-const==
  rule <expr>
         ...
         <k> (!abs! X) C:Const ~> E1 => !OPPONENT! </k>
         <eval> ES1 => E1 ~> ES1 </eval>
         <trace> TR1 => TR1 ~> pcall X C </trace>
         <step> S </step>
         ...
       </expr>
       <expr>
         ...
         <k> (!abs! X) C:Const ~> E2 => !OPPONENT! </k>
         <eval> ES2 => E2 ~> ES2 </eval>
         <trace> TR2 => TR2 ~> pcall X C </trace>
         <step> S </step>
         ...
       </expr>
       requires S >Int 0
       [transition]
  //==proponent-question-lambda==
  rule <expr>
         ...
         <k>
           (!abs! X) (fun X:KVar -> EX:Exp) ~> E1
           =>
           !OPPONENT!
         </k>
         <pub> ... .Map => (!I:Int |-> (fun X -> EX)) ... </pub>
         <eval> ES1 => E1 ~> ES1 </eval>
         <trace> TR1 => TR1 ~> pcall X (fun X -> EX) </trace>
         <step> S </step>
         ...
       </expr>
       <expr>
         ...
         <k>
           (!abs! X) (fun Y:KVar -> EY:Exp) ~> E2
           =>
           !OPPONENT!
         </k>
         <pub> ... .Map => (!I:Int |-> (fun Y -> EY)) ... </pub>
         <eval> ES2 => E2 ~> ES2 </eval>
         <trace> TR2 => TR2 ~> pcall X (fun Y -> EY) </trace>
         <step> S </step>
         ...
       </expr>
       requires S >Int 0
       [transition]
       
  //==OPPONENT-ANSWERS==
  // TODO: maybe use only Boolean constants.
  // TODO: we may need typing for SMT calls for symbolic integers.
  // TODO: how to deal with symbolic values? a variable?
  // TODO: should step counter be inside the process?
  //==opponent-answer-constant==
  rule <expr>
         ...
         <k> !OPPONENT! => !abs! !X:KVar ~> E1 </k>
         <eval> E1:KItem ~> ES1 => ES1 </eval>
         <trace> TR1 => TR1 ~> oret (!abs! !X) </trace>
         <step> S </step>
         ...
       </expr>
       <expr>
         ...
         <k> !OPPONENT! => !abs! !X ~> E2 </k>
         <eval> E2:KItem ~> ES2 => ES2 </eval>
         <trace> TR2 => TR2 ~> oret (!abs! !X) </trace>
         <step> S </step>
         ...
       </expr>
       requires S >Int 0
       [transition]
  //==opponent-answer-lambda==
  rule <expr>
         ...
         <k>
           !OPPONENT!
           =>
           (fun !X:KVar -> (!abs! !Y:KVar) !X) ~> E1
         </k>
         <eval> E1:KItem ~> ES1 => ES1 </eval>
         <trace> TR1 => TR1 ~> oret (fun !X -> (!abs! !Y) !X) </trace>
         <step> S </step>
         ...
       </expr>
       <expr>
         ...
         <k>
           !OPPONENT!
           =>
           (fun !X -> (!abs! !Y) !X) ~> E2
         </k>
         <eval> E2:KItem ~> ES2 => ES2 </eval>
         <trace> TR2 => TR2 ~> oret (fun !X -> (!abs! !Y) !X) </trace>
         <step> S </step>
         ...
       </expr>
       requires S >Int 0
       [transition]
  //==OPPONENT-QUESTIONS==
  //==opponent-question-const==
  rule <expr>
         ...
         <k> !OPPONENT! => EX1[!abs! !C:KVar/X1] </k>
         <pub> ... I |-> (fun X1 -> EX1) ... </pub>
         <trace> TR1 => TR1 ~> ocall I (!abs! !C) </trace>
         <step> S => S -Int 1 </step>
         ...
       </expr>
       <expr>
         ...
         <k> !OPPONENT! => EX2[!abs! !C/X2] </k>
         <pub> ... I |-> (fun X2 -> EX2) ... </pub>
         <trace> TR2 => TR2 ~> ocall I (!abs! !C) </trace>
         <step> S => S -Int 1 </step>
         ...
       </expr>
       requires S >Int 0
       [transition]
  //==proponent-question-lambda==
  rule <expr>
         ...
         <k>
           !OPPONENT!
           =>
           EX1[(fun !Y:KVar -> (!abs! !F:KVar))/X1]
         </k>
         <pub> ... I |-> (fun X1 -> EX1) ... </pub>
         <trace> TR1 => TR1 ~> ocall I (fun !Y -> (!abs! !F)) </trace>
         <step> S => S -Int 1 </step>
         ...
       </expr>
       <expr>
         ...
         <k>
           !OPPONENT!
           =>
           EX2[(fun !Y -> (!abs! !F))/X2]
         </k>
         <pub> ... I |-> (fun X2 -> EX2) ... </pub>
         <trace> TR2 => TR2 ~> ocall I (fun !Y -> (!abs! !F)) </trace>
         <step> S => S -Int 1 </step>
         ...
       </expr>
       requires S >Int 0
       [transition]
  //==proponent-nil==
  //==application-nil==
  rule <expr>
         ...
         <k> !OPPONENT! => _nil_ </k>
         <step> I </step>
         ...
       </expr>
       <expr>
         ...
         <k> !OPPONENT! => _nil_ </k>
         <step> S </step>
         ...
       </expr>
       requires S <=Int 0
       [transition]
  //TODO: implement termination checking mode
  //TODO: implement checking innequivalence at proponent move
  //TODO: remove multiplicity. Use two explicit expr cells and double the rules.
  //TODO: more to fix....
endmodule

