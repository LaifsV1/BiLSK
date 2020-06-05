require "substitution.k"

module BILS-SYNTAX
  imports DOMAINS-SYNTAX
  imports SUBSTITUTION

  syntax Exp ::= KVar | Val
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
               > Exp ";" Exp                          [strict(1), right]
               > "let" KVar "=" Exp "in" Exp          [binder, strict(2)]
               | "let rec" KVar "=" Exp "in" Exp      [binder, strict(2)]
               | "ref" KVar "=" Exp "in" Exp          [binder, strict(2)]
               | "fun" KVar "->" Exp                  [binder]
               | "(" Exp ")"                          [bracket]
  syntax Prog ::= Exp "||" Exp
                | "#bound" Int Exp "||" Exp 
  syntax Val ::= Const | "fun" KVar "->" Exp [binder]
  syntax Const ::= Int | Bool | "()"
endmodule

module BILS
  imports BILS-SYNTAX
  imports SUBSTITUTION
  imports COLLECTIONS
  imports DOMAINS
  imports SET

  syntax Mode ::= "_FAIL_" | "_OK_" | "_NIL_"
  syntax KResult ::= Val
  syntax Prog ::= Exp

  configuration 
      <T>
        <bisim>
          <m> _OK_  </m>
          <expr multiplicity="*">
            <k> $PGM:Prog </k>
            <state> .Map </state>
            <step> 10 </step>
          </expr>
        </bisim>
      </T>

  rule <expr>
       ...
       <k> #bound I:Int E1 || E2 => E1 </k>
       <step> _ => I </step>
       ...
       </expr>
       (.Bag => <expr>...<k> E2 </k><step> I </step>...</expr>)
  rule <expr>...<k> E1 || E2 => E1 </k>...</expr>
       (.Bag => <expr>...<k> E2 </k>...</expr>)

  // CONCRETE OPERATIONAL SEMANTICS:
  //==arithmetic==
  rule <expr>...<k> I1:Int +  I2:Int => I1 +Int  I2 ... </k>...</expr>
  rule <expr>...<k> I1:Int -  I2:Int => I1 -Int  I2 ... </k>...</expr>
  rule <expr>...<k> I1:Int *  I2:Int => I1 *Int  I2 ... </k>...</expr>
  rule <expr>...<k> I1:Int /  I2:Int => I1 /Int  I2 ... </k>...</expr>
  rule <expr>...<k> I1:Int >  I2:Int => I1 >Int  I2 ... </k>...</expr>
  rule <expr>...<k> I1:Int <  I2:Int => I1 <Int  I2 ... </k>...</expr>
  rule <expr>...<k> I1:Int >= I2:Int => I1 >=Int I2 ... </k>...</expr>
  rule <expr>...<k> I1:Int <= I2:Int => I1 <=Int I2 ... </k>...</expr>
  rule <expr>...<k> I1:Int == I2:Int => I1 ==Int I2 ... </k>...</expr>
  rule <expr>...<k> B1:Bool ==  B2:Bool => B1 ==Bool  B2 ... </k>...</expr>
  rule <expr>...<k> B1:Bool and B2:Bool => B1 andBool B2 ... </k>...</expr>
  rule <expr>...<k> B1:Bool or  B2:Bool => B1 orBool  B2 ... </k>...</expr>
  rule <expr>...<k> not B:Bool => notBool B ... </k>...</expr>
  //==conditionals==
  rule <expr>...<k> if true  then ET else EF => ET ... </k>...</expr>
  rule <expr>...<k> if false then ET else EF => EF ... </k>...</expr>
  //==application==
  rule <expr>...<k> (fun X:KVar -> E:Exp) V:Val => E[V/X] ... </k>...</expr>
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
  rule <k> V:Val ; E:Exp => E ... </k>
  //==let-binding==
  rule <k> let X:KVar = V:Val in E:Exp => E[V/X] ... </k>
  //==let-rec-binding==
  rule <k> let rec F:KVar = V:Val in E:Exp => E[V[let rec F = V in F/F]/F] ... </k>
endmodule

