requires "edsl.k"

module RULES
    imports EVM
    imports EDSL
    imports K-REFLECTION

// VERIFICATION.k

    rule #rangeUInt    (   1 ,      X ) => #range ( 0               <= X <= 1               ) [macro]

    syntax Int ::= nthbyteof ( Int , Int , Int ) [function, smtlib(smt_nthbyteof), proj]
 // ------------------------------------------------------------------------------
    rule nthbyteof(V, I, N) => nthbyteof(V /Int 256, I, N -Int 1) when N  >Int (I +Int 1) [concrete]
    rule nthbyteof(V, I, N) =>           V modInt 256             when N ==Int (I +Int 1) [concrete]

    rule bool2Word(notBool(A ==K 0)) => A
         requires #rangeUInt(1, A)

    //Blasphemy
    rule notBool(notBool(A)) => A

    rule 0 <=Int nthbyteof(V, I, N)          => true
    rule         nthbyteof(V, I, N) <Int 256 => true

    rule #asWord( nthbyteof(V,  0, 32)
                : nthbyteof(V,  1, 32)
                : nthbyteof(V,  2, 32)
                : nthbyteof(V,  3, 32)
                : nthbyteof(V,  4, 32)
                : nthbyteof(V,  5, 32)
                : nthbyteof(V,  6, 32)
                : nthbyteof(V,  7, 32)
                : nthbyteof(V,  8, 32)
                : nthbyteof(V,  9, 32)
                : nthbyteof(V, 10, 32)
                : nthbyteof(V, 11, 32)
                : nthbyteof(V, 12, 32)
                : nthbyteof(V, 13, 32)
                : nthbyteof(V, 14, 32)
                : nthbyteof(V, 15, 32)
                : nthbyteof(V, 16, 32)
                : nthbyteof(V, 17, 32)
                : nthbyteof(V, 18, 32)
                : nthbyteof(V, 19, 32)
                : nthbyteof(V, 20, 32)
                : nthbyteof(V, 21, 32)
                : nthbyteof(V, 22, 32)
                : nthbyteof(V, 23, 32)
                : nthbyteof(V, 24, 32)
                : nthbyteof(V, 25, 32)
                : nthbyteof(V, 26, 32)
                : nthbyteof(V, 27, 32)
                : nthbyteof(V, 28, 32)
                : nthbyteof(V, 29, 32)
                : nthbyteof(V, 30, 32)
                : nthbyteof(V, 31, 32)
                : .WordStack ) => V
      requires 0 <=Int V andBool V <Int pow256


    rule #asWord( nthbyteof(#unsigned(V),  0, 32)
                : nthbyteof(#unsigned(V),  1, 32)
                : nthbyteof(#unsigned(V),  2, 32)
                : nthbyteof(#unsigned(V),  3, 32)
                : nthbyteof(#unsigned(V),  4, 32)
                : nthbyteof(#unsigned(V),  5, 32)
                : nthbyteof(#unsigned(V),  6, 32)
                : nthbyteof(#unsigned(V),  7, 32)
                : nthbyteof(#unsigned(V),  8, 32)
                : nthbyteof(#unsigned(V),  9, 32)
                : nthbyteof(#unsigned(V), 10, 32)
                : nthbyteof(#unsigned(V), 11, 32)
                : nthbyteof(#unsigned(V), 12, 32)
                : nthbyteof(#unsigned(V), 13, 32)
                : nthbyteof(#unsigned(V), 14, 32)
                : nthbyteof(#unsigned(V), 15, 32)
                : nthbyteof(#unsigned(V), 16, 32)
                : nthbyteof(#unsigned(V), 17, 32)
                : nthbyteof(#unsigned(V), 18, 32)
                : nthbyteof(#unsigned(V), 19, 32)
                : nthbyteof(#unsigned(V), 20, 32)
                : nthbyteof(#unsigned(V), 21, 32)
                : nthbyteof(#unsigned(V), 22, 32)
                : nthbyteof(#unsigned(V), 23, 32)
                : nthbyteof(#unsigned(V), 24, 32)
                : nthbyteof(#unsigned(V), 25, 32)
                : nthbyteof(#unsigned(V), 26, 32)
                : nthbyteof(#unsigned(V), 27, 32)
                : nthbyteof(#unsigned(V), 28, 32)
                : nthbyteof(#unsigned(V), 29, 32)
                : nthbyteof(#unsigned(V), 30, 32)
                : nthbyteof(#unsigned(V), 31, 32)
                : .WordStack ) => #unsigned(V)
      requires #rangeSInt(256, V)

    rule #asWord( nthbyteof(keccakIntList(V),  0, 32)
                : nthbyteof(keccakIntList(V),  1, 32)
                : nthbyteof(keccakIntList(V),  2, 32)
                : nthbyteof(keccakIntList(V),  3, 32)
                : nthbyteof(keccakIntList(V),  4, 32)
                : nthbyteof(keccakIntList(V),  5, 32)
                : nthbyteof(keccakIntList(V),  6, 32)
                : nthbyteof(keccakIntList(V),  7, 32)
                : nthbyteof(keccakIntList(V),  8, 32)
                : nthbyteof(keccakIntList(V),  9, 32)
                : nthbyteof(keccakIntList(V), 10, 32)
                : nthbyteof(keccakIntList(V), 11, 32)
                : nthbyteof(keccakIntList(V), 12, 32)
                : nthbyteof(keccakIntList(V), 13, 32)
                : nthbyteof(keccakIntList(V), 14, 32)
                : nthbyteof(keccakIntList(V), 15, 32)
                : nthbyteof(keccakIntList(V), 16, 32)
                : nthbyteof(keccakIntList(V), 17, 32)
                : nthbyteof(keccakIntList(V), 18, 32)
                : nthbyteof(keccakIntList(V), 19, 32)
                : nthbyteof(keccakIntList(V), 20, 32)
                : nthbyteof(keccakIntList(V), 21, 32)
                : nthbyteof(keccakIntList(V), 22, 32)
                : nthbyteof(keccakIntList(V), 23, 32)
                : nthbyteof(keccakIntList(V), 24, 32)
                : nthbyteof(keccakIntList(V), 25, 32)
                : nthbyteof(keccakIntList(V), 26, 32)
                : nthbyteof(keccakIntList(V), 27, 32)
                : nthbyteof(keccakIntList(V), 28, 32)
                : nthbyteof(keccakIntList(V), 29, 32)
                : nthbyteof(keccakIntList(V), 30, 32)
                : nthbyteof(keccakIntList(V), 31, 32)
                : .WordStack ) => keccakIntList(V)

    rule #asWord( nthbyteof(#symEcrec(V),  0, 32)
                : nthbyteof(#symEcrec(V),  1, 32)
                : nthbyteof(#symEcrec(V),  2, 32)
                : nthbyteof(#symEcrec(V),  3, 32)
                : nthbyteof(#symEcrec(V),  4, 32)
                : nthbyteof(#symEcrec(V),  5, 32)
                : nthbyteof(#symEcrec(V),  6, 32)
                : nthbyteof(#symEcrec(V),  7, 32)
                : nthbyteof(#symEcrec(V),  8, 32)
                : nthbyteof(#symEcrec(V),  9, 32)
                : nthbyteof(#symEcrec(V), 10, 32)
                : nthbyteof(#symEcrec(V), 11, 32)
                : nthbyteof(#symEcrec(V), 12, 32)
                : nthbyteof(#symEcrec(V), 13, 32)
                : nthbyteof(#symEcrec(V), 14, 32)
                : nthbyteof(#symEcrec(V), 15, 32)
                : nthbyteof(#symEcrec(V), 16, 32)
                : nthbyteof(#symEcrec(V), 17, 32)
                : nthbyteof(#symEcrec(V), 18, 32)
                : nthbyteof(#symEcrec(V), 19, 32)
                : nthbyteof(#symEcrec(V), 20, 32)
                : nthbyteof(#symEcrec(V), 21, 32)
                : nthbyteof(#symEcrec(V), 22, 32)
                : nthbyteof(#symEcrec(V), 23, 32)
                : nthbyteof(#symEcrec(V), 24, 32)
                : nthbyteof(#symEcrec(V), 25, 32)
                : nthbyteof(#symEcrec(V), 26, 32)
                : nthbyteof(#symEcrec(V), 27, 32)
                : nthbyteof(#symEcrec(V), 28, 32)
                : nthbyteof(#symEcrec(V), 29, 32)
                : nthbyteof(#symEcrec(V), 30, 32)
                : nthbyteof(#symEcrec(V), 31, 32)
                : .WordStack ) => #symEcrec(V)


rule ACCTCODE in SetItem( 1 )
                 SetItem ( 2 )
                 SetItem ( 3 )
                 SetItem ( 4 )
                 SetItem ( 5 )
                 SetItem ( 6 )
                 SetItem ( 7 )
                 SetItem ( 8 )
                 => false
     requires 9 <=Int ACCTCODE


// for terms came from bytecode not via #hashedLocation
    rule keccak(WS) => keccakIntList(byteStack2IntList(WS))
      requires ( notBool #isConcrete(WS) )
       andBool ( #sizeWordStack(WS) ==Int 32 orBool #sizeWordStack(WS) ==Int 64 )

    rule 0 <=Int keccakIntList(N)     => true
    rule keccaktIntList(N) <Int pow256 => true


    rule #padToWidth(32, #asByteStack( #unsigned(V) )) => #asByteStackInWidth( #unsigned(V), 32)
      requires #rangeSInt(256, V)


    rule #padToWidth(32, #asByteStack(V)) => #asByteStackInWidth(V, 32)
      requires 0 <=Int V andBool V <Int pow256


    rule #padToWidth(32, #asByteStack( keccakIntList (V) )) => #asByteStackInWidth( keccakIntList (V), 32)

    rule #padToWidth(32, #asByteStack( #symEcrec(V) )) => #asByteStackInWidth( #symEcrec(V), 32)


   // for Vyper
    rule #padToWidth(N, #asByteStack(#asWord(WS))) => WS
      requires #sizeWordStack(WS) <=Int 32 andBool N ==Int #sizeWordStack(WS)

    // storing a symbolic boolean value in memory
    rule #padToWidth(32, #asByteStack(bool2Word(E)))
      => #asByteStackInWidthaux(0, 30, 32, nthbyteof(bool2Word(E), 31, 32) : .WordStack)

    // for Solidity
    rule #asWord(WS) /Int D => #asWord(#take(#sizeWordStack(WS) -Int log256Int(D), WS))
      requires D modInt 256 ==Int 0 andBool D >=Int 0
       andBool #sizeWordStack(WS) >=Int log256Int(D)
       andBool #sizeWordStack(WS) <=Int 32

    // for Solidity >= 0.5.6
    rule #asWord(WS) >>Int D => #asWord(#take(#sizeWordStack(WS) -Int (D /Int 8), WS))
     requires D modInt 8 ==Int 0 andBool D >=Int 0
       andBool #sizeWordStack(WS) >=Int (D /Int 8)
       andBool #sizeWordStack(WS) <=Int 32
    rule #sizeWordStack(#take(N, _)) => N
    rule #sizeWordStack(#take(N, _), M) => N +Int M

    syntax WordStack ::= #asByteStackInWidth    ( Int, Int )                 [function]
                       | #asByteStackInWidthaux ( Int, Int, Int, WordStack ) [function]
 // -----------------------------------------------------------------------------------
    rule #asByteStackInWidth(X, N) => #asByteStackInWidthaux(X, N -Int 1, N, .WordStack)

    rule #asByteStackInWidthaux(X, I, N, WS) => #asByteStackInWidthaux(X, I -Int 1, N, nthbyteof(X, I, N) : WS) when I >Int 0
    rule #asByteStackInWidthaux(X, 0, N, WS) => nthbyteof(X, 0, N) : WS

    rule 0 +Int N => N
    rule N +Int 0 => N

    rule N -Int 0 => N

    rule 1 *Int N => N
    rule N *Int 1 => N
    rule 0 *Int _ => 0
    rule _ *Int 0 => 0

    rule N /Int 1 => N
    rule N *Int A /Int A => N

    rule 0 |Int N => N
    rule N |Int 0 => N
    rule N |Int N => N

    rule 0 &Int N => 0
    rule N &Int 0 => 0
    rule N &Int N => N







    rule (I1 +Int I2) +Int I3 => I1 +Int (I2 +Int I3) when #isConcrete(I2) andBool #isConcrete(I3)
    rule (I1 +Int I2) -Int I3 => I1 +Int (I2 -Int I3) when #isConcrete(I2) andBool #isConcrete(I3)
    rule (I1 -Int I2) +Int I3 => I1 -Int (I2 -Int I3) when #isConcrete(I2) andBool #isConcrete(I3)
    rule (I1 -Int I2) -Int I3 => I1 -Int (I2 +Int I3) when #isConcrete(I2) andBool #isConcrete(I3)

    rule I1 &Int (I2 &Int I3) => (I1 &Int I2) &Int I3 when #isConcrete(I1) andBool #isConcrete(I2)

    // 0xffff...f &Int N = N
    rule MASK &Int N => N  requires MASK ==Int (2 ^Int (log2Int(MASK) +Int 1)) -Int 1 // MASK = 0xffff...f
                            andBool 0 <=Int N andBool N <=Int MASK

    // 0xffff...f &Int N = N
    rule N &Int MASK => N  requires MASK ==Int (2 ^Int (log2Int(MASK) +Int 1)) -Int 1 // MASK = 0xffff...f
                            andBool 0 <=Int N andBool N <=Int MASK


    // for gas calculation
    rule A -Int (#if C #then B1 #else B2 #fi) => #if C #then (A -Int B1) #else (A -Int B2) #fi

    rule (#if C #then B1 #else B2 #fi) -Int A => #if C #then (B1 -Int A) #else (B2 -Int A) #fi 
    rule (#if C #then B1 #else B2 #fi) +Int A => #if C #then (B1 +Int A) #else (B2 +Int A) #fi

    rule (#if C #then B1 #else B2 #fi) >Int A => true
       requires B1 >Int A andBool B2 >Int A

    rule (#if C #then B1 #else B2 #fi) >=Int A => true
       requires B1 >=Int A andBool B2 >=Int A

    rule #if C #then B1 #else B2 #fi ==K A => B1 ==Int A
       requires C

    rule #if C #then B1 #else B2 #fi ==K A => B2 ==Int A
       requires notBool C


    rule A -Int A => 0

    rule bool2Word(A) |Int bool2Word(B) => bool2Word(A  orBool B)
    rule bool2Word(A) &Int bool2Word(B) => bool2Word(A andBool B)

    rule bool2Word(A)  ==K 0 => notBool(A)
    rule bool2Word(A)  ==K 1 => A

    rule chop(bool2Word(B)) => bool2Word(B)





    rule 0 <=Int chop(V)             => true
    rule         chop(V) <Int pow256 => true

    rule 0 <=Int keccak(V)             => true
    rule         keccak(V) <Int pow256 => true

    rule 0 <=Int X &Int Y             => true requires 0 <=Int X andBool X <Int pow256 andBool 0 <=Int Y andBool Y <Int pow256
    rule         X &Int Y <Int pow256 => true requires 0 <=Int X andBool X <Int pow256 andBool 0 <=Int Y andBool Y <Int pow256





    rule chop(I) => I requires 0 <=Int I andBool I <Int pow256




    rule #sizeWordStack ( _ , _ ) >=Int 0 => true [smt-lemma]
    rule #sizeWordStack ( WS , N:Int )
      => #sizeWordStack ( WS , 0 ) +Int N
      requires N =/=K 0
      [lemma]

rule chop(#unsigned(W)) => #unsigned(W)
  requires #rangeSInt(256, W)

rule #signed(#unsigned(W)) => W
  requires #rangeSInt(256, W)

rule #unsigned(#signed(W)) => W
  requires #rangeUInt(256, W)

rule W0 s<Word W1 => #signed(W0) <Word #signed(W1)

rule   #signed(X) ==K   #signed(Y) => X ==K Y requires #rangeUInt(256,X) orBool #rangeUInt(256,Y)
rule #unsigned(X) ==K #unsigned(Y) => X ==K Y requires #rangeSInt(256,X) orBool #rangeSInt(256,Y)


rule A modInt pow160 => A
  requires #rangeAddress(A)

syntax Bool ::= #notPrecompileAddress ( Int ) [function]
// ---------------------------------------
rule #notPrecompileAddress ( X ) => 9 <=Int X andBool #rangeAddress(X)

// ABSTRACT SEMANTICS.k

  rule <k> LT W0 W1 => bool2Word(W0  <Int W1) ~> #push ... </k> [trusted]
  rule <k> GT W0 W1 => bool2Word(W0  >Int W1) ~> #push ... </k> [trusted]
  rule <k> EQ W0 W1 => bool2Word(W0 ==Int W1) ~> #push ... </k> [trusted]
  rule <k> ISZERO W => bool2Word(W  ==Int 0 ) ~> #push ... </k> [trusted]


//RULES MUST USE ==K and not ==Int
//Warning: assumes injective hashing
rule keccakIntList(A B .IntList) ==K keccakIntList(C D .IntList) => A ==Int C andBool B ==Int D

rule keccakIntList(A B C .IntList) ==K keccakIntList(D E F .IntList) => A ==Int D andBool B ==Int E andBool C ==Int F


rule keccakIntList(C) ==K A => false
     requires 0 <=Int A andBool A <=Int 20

rule keccakIntList(C) +Int B ==K A => false
     requires 0 <=Int A andBool A <=Int 20
     andBool 0 <=Int B andBool B <=Int 20

rule A ==K keccakIntList(C) +Int B => false
     requires 0 <=Int A andBool A <=Int 20
     andBool 0 <=Int B andBool B <=Int 20

rule keccakIntList(C) +Int B ==K keccakIntList(A) => false
     requires 0 <=Int B andBool B <=Int 20

rule keccakIntList(A) +Int B ==K keccakIntList(A) +Int C => false
     requires B =/=Int C

rule keccakIntList(A) +Int B ==K keccakIntList(C) +Int D => false
     requires B =/=K C


rule keccakIntList(A) ==K keccakIntList(C) +Int B => false
     requires 0 <=Int B andBool B <=Int 20


rule A ==K keccakIntList(C) => false
     requires 0 <=Int A andBool A <=Int 20

rule Cgascap(SCHED, GCAP, GAVAIL, GEXTRA) => #if GAVAIL <Int GEXTRA orBool Gstaticcalldepth << SCHED >> #then GCAP #else minInt(#allBut64th(GAVAIL -Int GEXTRA), GCAP) #fi

rule Csstore(SCHED, NEW, CURR, ORIG)
  => #if CURR ==Int NEW orBool ORIG =/=Int CURR #then Gsload < SCHED > #else #if ORIG ==Int 0 #then Gsstoreset < SCHED > #else Gsstorereset < SCHED > #fi #fi
  requires Ghasdirtysstore << SCHED >>

rule Csstore(SCHED, NEW, CURR, ORIG)
  => #if CURR ==Int 0 andBool NEW =/=Int 0 #then Gsstoreset < SCHED > #else Gsstorereset < SCHED > #fi
  requires notBool Ghasdirtysstore << SCHED >>

rule Rsstore(SCHED, NEW, CURR, ORIG) => #if CURR =/=Int 0 andBool NEW ==Int 0 #then Rsstoreclear < SCHED > #else 0 #fi
      requires notBool Ghasdirtysstore << SCHED >>

rule Cextra(SCHED, ISEMPTY, VALUE) => Gcall < SCHED > +Int Cnew(SCHED, ISEMPTY, VALUE) +Int Cxfer(SCHED, VALUE)

rule Cmem(SCHED, N) => (N *Int Gmemory < SCHED >) +Int ((N *Int N) /Int Gquadcoeff < SCHED >)

//Symbolic wrapper over the argument of #ecrec, no implementation.
syntax Int ::= #symEcrec ( WordStack ) [function]

rule <k> ECREC => #end EVMC_SUCCESS ... </k>
       <callData> DATA </callData>
       <output> _ => #ecrec(#symEcrec(DATA)) </output>
    requires notBool #isConcrete(DATA) andBool #sizeWordStack(DATA) ==Int 128
    [trusted]


// ./src/storage.k.md

syntax Int ::= "pow48"  [function]
syntax Int ::= "pow208" [function]
rule pow48  => 281474976710656                                                 [macro]
rule pow208 => 411376139330301510538742295639337626245683966408394965837152256 [macro]

syntax Int ::= "#WordPackUInt48UInt48" "(" Int "," Int ")" [function]
// ----------------------------------------------------------
rule #WordPackUInt48UInt48(X, Y) => Y *Int pow48 +Int X
  requires #rangeUInt(48, X)
  andBool #rangeUInt(48, Y)

syntax Int ::= "#WordPackAddrUInt48UInt48" "(" Int "," Int "," Int ")" [function]
// ----------------------------------------------------------------------
rule #WordPackAddrUInt48UInt48(A, X, Y) => Y *Int pow208 +Int X *Int pow160 +Int A
  requires #rangeAddress(A)
  andBool #rangeUInt(48, X)
  andBool #rangeUInt(48, Y)
// act: public
syntax Int ::= "#Vat.wards" "[" Int "]" [function]
// -----------------------------------------------
// doc: whether `$0` is an owner of `Vat`
// act: address `$0` is `. == 1 ? authorised : unauthorised`
rule #Vat.wards[A] => #hashedLocation("Solidity", 0, A)

syntax Int ::= "#Vat.can" "[" Int "][" Int "]" [function]
// -----------------------------------------------
// doc: whether `$1` can spend the resources of `$0`
// act: address `$0` has authorized `$1`
rule #Vat.can[A][B] => #hashedLocation("Solidity", 1, A B)

syntax Int ::= "#Vat.ilks" "[" Int "].Art" [function]
// ----------------------------------------------------
// doc: total debt units issued from `$0`
// act: `$0` has debt issuance `.`
rule #Vat.ilks[Ilk].Art => #hashedLocation("Solidity", 2, Ilk) +Int 0

syntax Int ::= "#Vat.ilks" "[" Int "].rate" [function]
// ----------------------------------------------------
// doc: debt unit rate of `$0`
// act: `$0` has debt unit rate `.`
rule #Vat.ilks[Ilk].rate => #hashedLocation("Solidity", 2, Ilk) +Int 1

syntax Int ::= "#Vat.ilks" "[" Int "].spot" [function]
// -----------------------------------------------
// doc: price with safety margin for `$0`
// act: `$0` has safety margin `.`
rule #Vat.ilks[Ilk].spot => #hashedLocation("Solidity", 2, Ilk) +Int 2

syntax Int ::= "#Vat.ilks" "[" Int "].line" [function]
// -----------------------------------------------
// doc: debt ceiling for `$0`
// act: `$0` has debt ceiling `.`
rule #Vat.ilks[Ilk].line => #hashedLocation("Solidity", 2, Ilk) +Int 3

syntax Int ::= "#Vat.ilks" "[" Int "].dust" [function]
// -----------------------------------------------
// doc: urn debt floor for `$0`
// act: `$0` has debt floor `.`
rule #Vat.ilks[Ilk].dust => #hashedLocation("Solidity", 2, Ilk) +Int 4

syntax Int ::= "#Vat.urns" "[" Int "][" Int "].ink" [function]
// ----------------------------------------------------------
// doc: locked collateral units in `$0` assigned to `$1`
// act: agent `$1` has `.` collateral units in `$0`
rule #Vat.urns[Ilk][Usr].ink => #hashedLocation("Solidity", 3, Ilk Usr)

syntax Int ::= "#Vat.urns" "[" Int "][" Int "].art" [function]
// ----------------------------------------------------------
// doc: debt units in `$0` assigned to `$1`
// act: agent `$1` has `.` debt units in `$0`
rule #Vat.urns[Ilk][Usr].art => #hashedLocation("Solidity", 3, Ilk Usr) +Int 1

syntax Int ::= "#Vat.gem" "[" Int "][" Int "]" [function]
// ---------------------------------------------
// doc: unlocked collateral in `$0` assigned to `$1`
// act: agent `$1` has `.` unlocked collateral in `$0`
rule #Vat.gem[Ilk][Usr] => #hashedLocation("Solidity", 4, Ilk Usr)

syntax Int ::= "#Vat.dai" "[" Int "]" [function]
// ---------------------------------------------
// doc: dai assigned to `$0`
// act: agent `$0` has `.` dai
rule #Vat.dai[A] => #hashedLocation("Solidity", 5, A)

syntax Int ::= "#Vat.sin" "[" Int "]" [function]
// ---------------------------------------------
// doc: system debt assigned to `$0`
// act: agent `$0` has `.` dai
rule #Vat.sin[A] => #hashedLocation("Solidity", 6, A)

syntax Int ::= "#Vat.debt" [function]
// ---------------------------------
// doc: total dai issued from the system
// act: there is `.` dai in total
rule #Vat.debt => 7

syntax Int ::= "#Vat.vice" [function]
// ----------------------------------
// doc: total system debt
// act: there is `.` system debt
rule #Vat.vice => 8

syntax Int ::= "#Vat.Line" [function]
// ----------------------------------
// doc: global debt ceiling
// act: the global debt ceiling is `.`
rule #Vat.Line => 9

syntax Int ::= "#Vat.live" [function]
// ----------------------------------
// doc: system status
// act: the system is `. == 1 ? : not` live
rule #Vat.live => 10
syntax Int ::= "#Dai.wards" "[" Int "]" [function]
// -----------------------------------------------
// doc: whether `$0` is an owner of `Vat`
// act: address `$0` is `. == 1 ? authorised : unauthorised`
rule #Dai.wards[A] => #hashedLocation("Solidity", 0, A)

syntax Int ::= "#Dai.decimals" [function]
// -----------------------------------------------
// doc: decimal places in token balances
// act: The dai token has .` decimal places
rule #Dai.decimals => 1

syntax Int ::= "#Dai.name" [function]
// -----------------------------------------------
// doc: the Token name
// act: this token is called .`
rule #Dai.name => 2

syntax Int ::= "#Dai.symbol" [function]
// -----------------------------------------------
// doc: the Token symbol
// act: this token has symbol .`
rule #Dai.symbol => 3

syntax Int ::= "#Dai.version" [function]
// -----------------------------------------------
// doc: the Token name
// act: this token is version .`
rule #Dai.version => 4

syntax Int ::= "#Dai.totalSupply" [function]
// -----------------------------------------------
// doc: the total supply of this token
// act: the total supply is .`
rule #Dai.totalSupply => 5

syntax Int ::= "#Dai.balanceOf" "[" Int "]" [function]
// -----------------------------------------------
// doc: the balance of a user
// act: the balance of `$0 is .` us ,
rule #Dai.balanceOf[A] => #hashedLocation("Solidity", 6, A)

syntax Int ::= "#Dai.allowance" "[" Int "][" Int "]" [function]
// -----------------------------------------------
// doc: the amount that can be spent on someones behalf
// act: `$1 can spend `.` tokens belonging to `$0`
rule #Dai.allowance[A][B] => #hashedLocation("Solidity", 7, A B)

syntax Int ::= "#Dai.nonces" "[" Int "]" [function]
// -----------------------------------------------
// doc: the amount that can be spent on someones behalf
// act: `$1 can spend `.` tokens belonging to `$0`
rule #Dai.nonces[A] => #hashedLocation("Solidity", 8, A)

syntax Int ::= "#Dai.DOMAIN_SEPARATOR" [function]
// -----------------------------------------------
// doc: the amount that can be spent on someones behalf
// act: `$1 can spend `.` tokens belonging to `$0`
rule #Dai.DOMAIN_SEPARATOR => 9
syntax Int ::= "#Jug.wards" "[" Int "]" [function]
// -----------------------------------------------
// doc: whether `$0` is an owner of `Jug`
// act: address `$0` is `. == 1 ? authorised : unauthorised`
rule #Jug.wards[A] => #hashedLocation("Solidity", 0, A)

syntax Int ::= "#Jug.ilks" "[" Int "].duty" [function]
// ----------------------------------------------------
// doc:
// act:
rule #Jug.ilks[Ilk].duty => #hashedLocation("Solidity", 1, Ilk) +Int 0

syntax Int ::= "#Jug.ilks" "[" Int "].rho" [function]
// ----------------------------------------------------
// doc:
// act:
rule #Jug.ilks[Ilk].rho => #hashedLocation("Solidity", 1, Ilk) +Int 1

syntax Int ::= "#Jug.vat" [function]
// ----------------------------------
// doc: `Vat` that this `Jug` points to
// act: this Jug points to Vat `.`
rule #Jug.vat => 2

syntax Int ::= "#Jug.vow" [function]
// ----------------------------------
// doc: `Vow` that this `Jug` points to
// act: this Jug points to Vow `.`
rule #Jug.vow => 3

syntax Int ::= "#Jug.base" [function]
// ----------------------------------
// doc:
// act:
rule #Jug.base => 4
syntax Int ::= "#Drip.wards" "[" Int "]" [function]
// -----------------------------------------------
// doc: whether `$0` is an owner of `Drip`
// act: address `$0` is `. == 1 ? authorised : unauthorised`
rule #Drip.wards[A] => #hashedLocation("Solidity", 0, A)

syntax Int ::= "#Drip.ilks" "[" Int "].tax" [function]
// ----------------------------------------------------
// doc: stability fee of `$0`
// act: `$0` has stability fee `.`
rule #Drip.ilks[Ilk].tax => #hashedLocation("Solidity", 1, Ilk) +Int 0

syntax Int ::= "#Drip.ilks" "[" Int "].rho" [function]
// ----------------------------------------------------
// doc: last drip time of `$0`
// act: `$0` was dripped at `.`
rule #Drip.ilks[Ilk].rho => #hashedLocation("Solidity", 1, Ilk) +Int 1

syntax Int ::= "#Drip.vat" [function]
// ----------------------------------
// doc: `Vat` that this `Drip` points to
// act: this Drip points to Vat `.`
rule #Drip.vat => 2

syntax Int ::= "#Drip.vow" [function]
// ----------------------------------
// doc: `Vow` that this `Drip` points to
// act: this Drip points to Vow `.`
rule #Drip.vow => 3

syntax Int ::= "#Drip.repo" [function]
// -----------------------------------
// doc: base interest rate
// act: the base interest rate is `.`
rule #Drip.repo => 4
syntax Int ::= "#Vow.wards" "[" Int "]" [function]
// ---------------------------------
// doc: whether `$0` is an owner of `Vow`
// act: address `$0` is `. == 1 ? authorised : unauthorised`
rule #Vow.wards[A] => #hashedLocation("Solidity", 0, A)

syntax Int ::= "#Vow.vat" [function]
// ---------------------------------
// doc: `Vat` that this `Vow` points to
// act: this Vow points to Vat `.`
rule #Vow.vat => 1

syntax Int ::= "#Vow.cow" [function]
// ---------------------------------
// doc: `Flapper` that this `Vow` points to
// act: this Vow points to Flapper `.`
rule #Vow.cow => 2

syntax Int ::= "#Vow.row" [function]
// ---------------------------------
// doc: `Flopper` that this `Vow` points to
// act: this Vow points to Flopper `.`
rule #Vow.row => 3

syntax Int ::= "#Vow.sin" "[" Int "]" [function]
// ---------------------------------------------
// doc: sin queued at timestamp `$0`
// act: `.` sin queued at timestamp `$0`
rule #Vow.sin[A] => #hashedLocation("Solidity", 4, A)

syntax Int ::= "#Vow.Sin" [function]
// ---------------------------------
// doc: total queued sin
// act: the total queued sin is `.`
rule #Vow.Sin => 5

syntax Int ::= "#Vow.Ash" [function]
// ---------------------------------
// doc: total sin in debt auctions
// act: the total sin in debt auctions is `.`
rule #Vow.Ash => 6

syntax Int ::= "#Vow.wait" [function]
// ----------------------------------
// doc: sin maturation time
// act: the sin maturation time is `.`
rule #Vow.wait => 7

syntax Int ::= "#Vow.sump" [function]
// ----------------------------------
// doc: debt auction lot size
// act: the debt auction lot size is `.`
rule #Vow.sump => 8

syntax Int ::= "#Vow.bump" [function]
// ----------------------------------
// doc: surplus auction lot size
// act: the surplus auction lot size is `.`
rule #Vow.bump => 9

syntax Int ::= "#Vow.hump" [function]
// ---------------------------------
// doc: surplus dai cushion
// act: the surplus dai cushion is `.`
rule #Vow.hump => 10
syntax Int ::= "#Cat.wards" "[" Int "]" [function]
// ---------------------------------
// doc: whether `$0` is an owner of `Cat`
// act: address `$0` is `. == 1 ? authorised : unauthorised`
rule #Cat.wards[A] => #hashedLocation("Solidity", 0, A)

syntax Int ::= "#Cat.ilks" "[" Int "].flip" [function]
// ---------------------------------------------------
// doc: `Flipper` for `$0`
// act:
rule #Cat.ilks[Ilk].flip => #hashedLocation("Solidity", 1, Ilk) +Int 0

syntax Int ::= "#Cat.ilks" "[" Int "].chop" [function]
// ---------------------------------------------------
// doc: liquidation penalty for `$0`
// act:
rule #Cat.ilks[Ilk].chop => #hashedLocation("Solidity", 1, Ilk) +Int 1

syntax Int ::= "#Cat.ilks" "[" Int "].lump" [function]
// ---------------------------------------------------
// doc: liquidation lot size for `$0`
// act:
rule #Cat.ilks[Ilk].lump => #hashedLocation("Solidity", 1, Ilk) +Int 2

syntax Int ::= "#Cat.flips" "[" Int "].ilk" [function]
// ---------------------------------------------------
// doc: collateral type for flip `$0`
// act:
rule #Cat.flips[N].ilk => #hashedLocation("Solidity", 2, N) +Int 0

syntax Int ::= "#Cat.flips" "[" Int "].urn" [function]
// ---------------------------------------------------
// doc: owner identifier for flip `$0`
// act:
rule #Cat.flips[N].urn => #hashedLocation("Solidity", 2, N) +Int 1

syntax Int ::= "#Cat.flips" "[" Int "].ink" [function]
// ---------------------------------------------------
// doc: collateral in flip `$0`
// act:
rule #Cat.flips[N].ink => #hashedLocation("Solidity", 2, N) +Int 2

syntax Int ::= "#Cat.flips" "[" Int "].tab" [function]
// ---------------------------------------------------
// doc: debt in flip `$0`
// act:
rule #Cat.flips[N].tab => #hashedLocation("Solidity", 2, N) +Int 3

syntax Int ::= "#Cat.nflip" [function]
// -----------------------------------
// doc: flip count
// act:
rule #Cat.nflip => 3

syntax Int ::= "#Cat.live" [function]
// ----------------------------------
// doc: system liveness
// act:
rule #Cat.live => 4

syntax Int ::= "#Cat.vat" [function]
// ---------------------------------
// doc: `Vat` that this `Cat` points to
// act:
rule #Cat.vat => 5

syntax Int ::= "#Cat.pit" [function]
// ---------------------------------
// doc: `Pit` that this `Cat` points to
// act:
rule #Cat.pit => 6

syntax Int ::= "#Cat.vow" [function]
// ---------------------------------
// doc: `Vow` that this `Cat` points to
// act:
rule #Cat.vow => 7
syntax Int ::= "#GemJoin.vat" [function]
// -------------------------------------
// doc: `Vat` that this adapter points to
// act:
rule #GemJoin.vat => 0

syntax Int ::= "#GemJoin.ilk" [function]
// -------------------------------------
// doc: collateral type of this adapter
// act:
rule #GemJoin.ilk => 1

syntax Int ::= "#GemJoin.gem" [function]
// -------------------------------------
// doc: underlying token of this adapter
// act:
rule #GemJoin.gem => 2
syntax Int ::= "#ETHJoin.vat" [function]
// -------------------------------------
// doc: `Vat` that this adapter points to
// act:
rule #ETHJoin.vat => 0

syntax Int ::= "#ETHJoin.ilk" [function]
// -------------------------------------
// doc: collateral type of this adapter
// act:
rule #ETHJoin.ilk => 1
syntax Int ::= "#DaiJoin.vat" [function]
// -------------------------------------
// doc: `Vat` that this adapter points to
// act:
rule #DaiJoin.vat => 0

syntax Int ::= "#DaiJoin.dai" [function]
// -------------------------------------
// doc: underlying dai token of this adapter
// act:
rule #DaiJoin.dai => 1
// packed, use #WordPackUInt48UInt48 to unpack this
syntax Int ::= "#Flipper.ttl_tau" [function]
// -----------------------------------------
// doc:
// act:
rule #Flipper.ttl_tau => 3

syntax Int ::= "#Flipper.kicks" [function]
// ---------------------------------------
// doc: auction counter
// act:
rule #Flipper.kicks => 4

syntax Int ::= "#Flipper.bids" "[" Int "].bid" [function]
// ------------------------------------------------------
// doc: current bid (dai)
// act:
rule #Flipper.bids[N].bid => #hashedLocation("Solidity", 5, N) +Int 0

syntax Int ::= "#Flipper.bids" "[" Int "].lot" [function]
// ------------------------------------------------------
// doc: current lot (gem)
// act:
rule #Flipper.bids[N].lot => #hashedLocation("Solidity", 5, N) +Int 1

// packed, use #WordPackAddrUInt48UInt48 to unpack this
syntax Int ::= "#Flipper.bids" "[" Int "].usr_tic_end" [function]
// --------------------------------------------------------------
// doc:
// act:
rule #Flipper.bids[N].usr_tic_end => #hashedLocation("Solidity", 5, N) +Int 2

syntax Int ::= "#Flipper.bids" "[" Int "].urn" [function]
// ------------------------------------------------------
// doc: beneficiary of remaining gems
// act:
rule #Flipper.bids[N].urn => #hashedLocation("Solidity", 5, N) +Int 3

syntax Int ::= "#Flipper.bids" "[" Int "].gal" [function]
// ------------------------------------------------------
// doc: beneficiary of dai
// act:
rule #Flipper.bids[N].gal => #hashedLocation("Solidity", 5, N) +Int 4

syntax Int ::= "#Flipper.bids" "[" Int "].tab" [function]
// ------------------------------------------------------
// doc: debt to cover
// act:
rule #Flipper.bids[N].tab => #hashedLocation("Solidity", 5, N) +Int 5
syntax Int ::= "#Flopper.wards" "[" Int "]" [function]
// ---------------------------------------
// doc: whether `$0` is an owner of `Flop`
// act: address `$0` is `. == 1 ? authorised : unauthorised`
rule #Flopper.wards[A] => #hashedLocation("Solidity", 0, A)

// packed, use #WordPackUInt48UInt48 to unpack this
syntax Int ::= "#Flopper.ttl_tau" [function]
// -----------------------------------------
// doc:
// act:
rule #Flopper.ttl_tau => 5

syntax Int ::= "#Flopper.kicks" [function]
// ---------------------------------------
// doc: auction counter
// act:
rule #Flopper.kicks => 6

syntax Int ::= "#Flopper.bids" "[" Int "].bid" [function]
// ------------------------------------------------------
// doc: current bid (dai)
// act:
rule #Flopper.bids[N].bid => #hashedLocation("Solidity", 1, N) +Int 0

syntax Int ::= "#Flopper.bids" "[" Int "].lot" [function]
// ------------------------------------------------------
// doc: current lot (gem)
// act:
rule #Flopper.bids[N].lot => #hashedLocation("Solidity", 1, N) +Int 1

// packed, use #WordPackAddrUInt48UInt48 to unpack this
syntax Int ::= "#Flopper.bids" "[" Int "].usr_tic_end" [function]
// --------------------------------------------------------------
// doc:
// act:
rule #Flopper.bids[N].usr_tic_end => #hashedLocation("Solidity", 1, N) +Int 2

syntax Int ::= "#Flopper.bids" "[" Int "].vow" [function]
// ------------------------------------------------------
// doc: beneficiary of the auction
// act:
rule #Flopper.bids[N].vow => #hashedLocation("Solidity", 1, N) +Int 3
syntax Int ::= "#Flapper.bids" "[" Int "].bid" [function]
// ------------------------------------------------------
// doc: current bid (dai)
// act:
rule #Flapper.bids[N].bid => #hashedLocation("Solidity", 0, N) +Int 0

syntax Int ::= "#Flapper.bids" "[" Int "].lot" [function]
// ------------------------------------------------------
// doc: current lot (gem)
// act:
rule #Flapper.bids[N].lot => #hashedLocation("Solidity", 0, N) +Int 1

// packed, use #WordPackAddrUInt48UInt48 to unpack this
syntax Int ::= "#Flapper.bids" "[" Int "].usr_tic_end" [function]
// --------------------------------------------------------------
// doc:
// act:
rule #Flapper.bids[N].usr_tic_end => #hashedLocation("Solidity", 0, N) +Int 2

syntax Int ::= "#Flapper.bids" "[" Int "].gal" [function]
// ------------------------------------------------------
// doc: beneficiary of the auction
// act:
rule #Flapper.bids[N].gal => #hashedLocation("Solidity", 0, N) +Int 3

syntax Int ::= "#Flapper.dai" [function]
// ---------------------------------------
// doc: dai token
// act:
rule #Flapper.dai => 1

syntax Int ::= "#Flapper.gem" [function]
// ---------------------------------------
// doc: mkr token
// act:
rule #Flapper.gem => 2

syntax Int ::= "#Flapper.beg" [function]
// ---------------------------------------
// doc: minimum bid increment
// act:
rule #Flapper.gem => 3

// packed, use #WordPackUInt48UInt48 to unpack this
syntax Int ::= "#Flapper.ttl_tau" [function]
// -----------------------------------------
// doc:
// act:
rule #Flapper.ttl_tau => 4

syntax Int ::= "#Flapper.kicks" [function]
// ---------------------------------------
// doc: auction counter
// act:
rule #Flapper.kicks => 5
syntax Int ::= "#Gem.balances" "[" Int "]" [function]
// --------------------------------------------------
// doc: `gem` balance of `$0`
// act:
rule #Gem.balances[A] => #hashedLocation("Solidity", 1, A)
// ./src/lemmas.k.md

syntax Int ::= num0 ( Int ) [function, smtlib(smt_num0)]
syntax Int ::= num1 ( Int ) [function, smtlib(smt_num1)]

rule num0(N) >=Int 0 => num0(N) >=Int 1
  requires N >=Int 1
  andBool N modInt 2 ==Int 0

rule num1(N) >=Int 0 => num1(N) >=Int 1
  requires N >Int 1
  andBool N modInt 2 =/=Int 0

rule num0(N /Int 2) => num0(N) -Int 1
  requires N >=Int 1
  andBool N modInt 2 ==Int 0

rule num0(N /Int 2) => num0(N)
  requires N >=Int 1
  andBool N modInt 2 ==Int 1

rule num1(N /Int 2) => num1(N) -Int 1
  requires N >Int 1
  andBool N modInt 2 ==Int 1

rule num1(N /Int 2) => num1(N)
  requires N >Int 1
  andBool N modInt 2 ==Int 0

rule num0(N) => 0
  requires N ==Int 1

rule num1(N) => 0
  requires N ==Int 1

syntax Int ::= "#string2Word" "(" String ")" [function]
// ----------------------------------------------------
rule #string2Word(S) => #asWord(#padRightToWidth(32, #parseByteStackRaw(S)))
syntax Int ::= "#Wad" [function]
// -----------------------------
rule #Wad => 1000000000000000000

syntax Int ::= "#Ray" [function]
// -----------------------------
rule #Ray => 1000000000000000000000000000
syntax Int ::= "#rmul" "(" Int "," Int ")" [function]

syntax Int ::= "#rpow" "(" Int "," Int "," Int "," Int ")"  [function, smtlib(smt_rpow), smt-prelude]

syntax Int ::= "#ifInt" Bool "#then" Int "#else" Int "#fi" [function, smtlib(ite), hook(KEQUAL.ite)]

rule A *Int C /Int C => A
  requires A *Int C <Int pow256

rule (X *Int Y) /Word Y => #ifInt Y ==Int 0 #then 0 #else chop(X) #fi

rule A /Int B <Int pow256 => true
  requires A <Int pow256

rule Z *Int (X ^Int N) => Z
  requires N ==Int 0

rule Z *Int (X ^Int (N %Int 2)) => Z
  requires N ==Int 0

rule 0 ^Int N => 1
  requires N ==Int 0

rule 0 ^Int N => 0
  requires N >Int 0

rule 0 <=Int (N /Int 2) => true
  requires 0 <=Int N

rule N /Int 2 <Int pow256 => true
  requires N <Int pow256

// TODO - review - do i need it?
rule chop(X *Int X) => X *Int X
  requires #rpow(Z, X, N, B) *Int B <Int pow256
  andBool N >=Int 2


rule #rpow(Z, X, 0, Base) => Z

rule #rpow(Z, X, N, Base) => Z
  requires N modInt 2 ==Int 0
  andBool N /Int 2 ==Int 0

rule #rpow(Z, 0, N, Base) => 0

rule #rpow(Base, X, N, Base) => X
  requires N ==Int 1

rule #rpow(((Z *Int X) +Int Half) /Int Base, X, N /Int 2, Base) =>
     #rpow(Z,                                 X, N,       Base)
  requires Half ==Int Base /Int 2
  andBool  N ==Int 1

rule #rpow(((Z *Int X) +Int Half) /Int Base, ((X *Int X) +Int Half) /Int Base, N /Int 2, Base) =>
     #rpow( Z                               , X                               , N       , Base )
  requires N modInt 2 =/=Int 0
  andBool  N >=Int 2
  andBool Half ==Int Base /Int 2

rule #rpow( Z                              , ((X *Int X) +Int Half) /Int Base, N /Int 2, Base) =>
     #rpow( Z                              , X                               , N       , Base )
  requires N modInt 2 ==Int 0
  andBool  N >=Int 2
andBool Half ==Int Base /Int 2

rule #rpow( X                              , ((X *Int X) +Int Half) /Int Base, N /Int 2, Base) =>
     #rpow( Base                           , X                               , N       , Base )
  requires N modInt 2 =/=Int 0
  andBool  N /Int 2 =/=Int 0
  andBool  Half ==Int Base /Int 2

rule Z *Int X <Int pow256 => true
  requires #rpow(Z, X, N, Base) <Int pow256
// hashed storage offsets never overflow (probabilistic assumption):
rule chop(keccakIntList(L) +Int N) => keccakIntList(L) +Int N
  requires N <=Int 100

// solidity also needs:
rule chop(keccakIntList(L)) => keccakIntList(L)
// and
rule chop(N +Int keccakIntList(L)) => keccakIntList(L) +Int N
  requires N <=Int 100
syntax Int ::= "MaskLast20" [function]
syntax Int ::= "MaskFirst6" [function]
syntax Int ::= "MaskFirst26" [function]
// -----------------------------------
// 0xffffffffffffffffffffffff0000000000000000000000000000000000000000
rule MaskLast20 => 115792089237316195423570985007226406215939081747436879206741300988257197096960 [macro]
// 0x000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffff
rule MaskFirst6 => 411376139330301510538742295639337626245683966408394965837152255                [macro]
// 0x0000000000000000000000000000000000000000000000000000ffffffffffff
rule MaskFirst26 => 281474976710655                                                               [macro]

rule MaskLast20 &Int A => 0
  requires #rangeAddress(A)

rule X |Int 0 => X

rule chop(A &Int B) => A &Int B
  requires #rangeUInt(256, A)
  andBool #rangeUInt(256, B)

rule chop(A |Int B) => A |Int B
  requires #rangeUInt(256, A)
  andBool #rangeUInt(256, B)

// Masking for packed words
rule MaskLast20 &Int (Y *Int pow208 +Int X *Int pow160 +Int A) => Y *Int pow208 +Int X *Int pow160
  requires #rangeAddress(A)
  andBool #rangeUInt(48, X)
  andBool #rangeUInt(48, Y)

rule B |Int (Y *Int pow208 +Int X *Int pow160) => Y *Int pow208 +Int X *Int pow160 +Int B
  requires #rangeAddress(B)
  andBool #rangeUInt(48, X)
  andBool #rangeUInt(48, Y)

rule (Y *Int pow208 +Int X *Int pow160 +Int A) /Int pow208 => Y
  requires #rangeAddress(A)
  andBool #rangeUInt(48, X)
  andBool #rangeUInt(48, Y)

rule (Y *Int pow48 +Int X) /Int pow48 => Y
  requires #rangeUInt(48, X)
  andBool #rangeUInt(48, Y)

rule MaskFirst6 &Int (X *Int pow208 +Int Y *Int pow160 +Int A) => Y *Int pow160 +Int A
  requires #rangeUInt(48, X)
  andBool #rangeUInt(48, Y)
  andBool #rangeAddress(A)

rule (X *Int pow208) |Int (Y *Int pow160 +Int A) => (X *Int pow208 +Int Y *Int pow160 +Int A)
  requires #rangeUInt(48, X)
  andBool #rangeUInt(48, Y)
  andBool #rangeAddress(A)

// rule MaskFirst26 &Int X => X
//   requires #rangeUInt(48, X)
rule WS ++ .WordStack => WS

rule #sizeWordStack ( #padToWidth ( 32 , #asByteStack ( #unsigned ( W ) ) ) , 0) => 32
  requires #rangeSInt(256, W)

// custom ones:
rule #asWord(#padToWidth(32, #asByteStack(#unsigned(X)))) => #unsigned(X)
  requires #rangeSInt(256, X)

// rule #take(N, #padToWidth(N, WS) ++ WS' ) => #padToWidth(N, WS)

// potentially useful
// rule #padToWidth(N, WS) ++ WS' => #padToWidth(N + #sizeWordStack(WS'), WS ++ WS')
// and the N, M versions

rule #take(N, #padToWidth(N, WS) ) => #padToWidth(N, WS)
rule notBool((MaskFirst26 &Int (A +Int B)) <Int A) => A +Int B <=Int maxUInt48
  requires #rangeUInt(48, A)
  andBool #rangeUInt(48, B)
rule #unsigned(X) ==K 0 => X ==Int 0
  requires #rangeSInt(256, X)

// rule 0 <Int #unsigned(X) => 0 <Int X
//   requires #rangeSInt(256, X)

// uadd
// lemmas for necessity
rule notBool(chop(A +Int B) <Int A) => A +Int B <=Int maxUInt256
  requires #rangeUInt(256, A)
  andBool #rangeUInt(256, B)

// usub
// lemmas for necessity
rule notBool(A -Word B >Int A) => (A -Int B >=Int minUInt256)
  requires #rangeUInt(256, A)
  andBool #rangeUInt(256, B)

// addui
// lemmas for sufficiency
rule chop(A +Int #unsigned(B)) => A +Int B
  requires #rangeUInt(256, A)
  andBool #rangeSInt(256, B)
  andBool #rangeUInt(256, A +Int B)

// lemmas for necessity
// rule chop(A +Int #unsigned(B)) >Int A => (A +Int B <=Int maxUInt256)
//   requires #rangeUInt(256, A)
//   andBool #rangeSInt(256, B)
//   andBool B >=Int 0

rule chop(A +Int B) >Int A => (A +Int B <=Int maxUInt256)
  requires #rangeUInt(256, A)
  andBool #rangeUInt(256, B)

rule (A +Int #unsigned(B) <=Int maxUInt256) => (A +Int B <=Int maxUInt256)
  requires #rangeUInt(256, A)
  andBool #rangeSInt(256, B)
  andBool B >=Int 0

rule chop(A +Int #unsigned(B)) <Int A => (A +Int B >=Int minUInt256)
  requires #rangeUInt(256, A)
  andBool #rangeSInt(256, B)
  andBool B <Int 0

// subui
// lemmas for sufficiency
rule A -Word #unsigned(B) => A -Int B
  requires #rangeUInt(256, A)
  andBool #rangeSInt(256, B)
  andBool #rangeUInt(256, A -Int B)

// lemmas for necessity
// rule A -Word #unsigned(B) <Int A => (A -Int B >=Int minUInt256)
//   requires #rangeUInt(256, A)
//   andBool #rangeSInt(256, B)
//   andBool B >=Int 0

rule A -Word B <Int A => (A -Int B >=Int minUInt256)
  requires #rangeUInt(256, A)
  andBool #rangeUInt(256, B)

rule (A -Int #unsigned(B) >=Int minUInt256) => (A -Int B >=Int minUInt256)
  requires #rangeUInt(256, A)
  andBool #rangeSInt(256, B)
  andBool B >=Int 0

rule A -Word #unsigned(B) >Int A => (A -Int B <=Int maxUInt256)
  requires #rangeUInt(256, A)
  andBool #rangeSInt(256, B)
  andBool B <Int 0

// mului
// lemmas for sufficiency
rule A *Int #unsigned(B) => #unsigned(A *Int B)
  requires #rangeUInt(256, A)
  andBool #rangeSInt(256, B)
  andBool #rangeSInt(256, A *Int B)

rule abs(#unsigned(A *Int B)) /Int abs(#unsigned(B)) => A
  requires #rangeUInt(256, A)
  andBool #rangeSInt(256, B)
  andBool #rangeSInt(256, A *Int B)
  andBool notBool (#unsigned(B) ==Int 0)

rule sgn(#unsigned(A *Int B)) *Int sgn(#unsigned(B)) => 1
  requires #rangeSInt(256, B)
  andBool #rangeUInt(256, A)
  andBool #rangeSInt(256, A)
  andBool #rangeSInt(256, A *Int B)

rule abs(B) ==K 0 => B ==K 0

// lemmas for necessity
rule #signed(X) <Int 0 => #rangeSInt(256, X)
   requires #rangeUInt(256, X)

rule A ==K 0 => false
requires notBool (#rangeSInt(256, B) andBool #rangeSInt(256, A *Int B))
     andBool #rangeSInt(256, B)

rule (#sgnInterp(sgn(chop(A *Int #unsigned(B))) *Int sgn(#unsigned(B)), chop(abs(chop(A *Int #unsigned(B))) /Int abs(#unsigned(B)))) ==K A) => false
  requires #rangeUInt(256, A)
  andBool #rangeSInt(256, B)
  andBool B =/=Int 0
  andBool notBool #rangeSInt(256, A *Int B)

endmodule
