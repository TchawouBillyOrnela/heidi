import LogicKit


//definition des mots du langage de heidi

let deponer = Value ("deponer")
let dretg = Value ("dretg")
let sanester = Value ("sanester")
let davent = Value ("davent")
let davos = Value ("davos")
let plaun = Value ("plaun")
let returnar = Value ("retournar")
let safermar = Value ("sa fermar")


//definition des mots du langage de tita
let court = Value ("court")
let whee = Value ("whee")
let who = Value ("who")
let wheet = Value ("wheet")
let wheeo = Value ("wheeo")
let hee = Value ("hee")
let long = Value ("long")

//on definit pause comme un mot de la syntaxe de Heidi et de tita
let pause = Value ("pause")
//syntaxe:
/*

Heidi:

inst  € {deponer,dretg,sanester,davent,davos,plaun,returnar,safermar}
_______________________________________________________________________
inst € ordreHeidi

inst1, inst2 € ordreHeidi
___________________________
inst1::pause::inst2 € ordreHeidi



Tita:

inst  € {court:: court ,whee::who ,wheet::wheeo , wheet::wheeo::wheet::wheet,who::hee::who,hee::hee::hee::hee,whee::whee::wheet,long}
__________________________________________________________________________________________________________________________________________
inst € ordreTita

inst1, inst2 € ordreTita
___________________________
inst1::pause::inst2 € ordreTita

*/




//semantique d'un ordre de Heidi regles d'inferences
/*
//on definit la syntaxe pour un ordre qui n'est  pas une liste:

___________________________         ,   _______________________________   ...
deponer =ordreHeidi=> court::court       dretg=ordreHeidi=> whee::who


//on definit la syntaxe pour un ordre qui est une succession d'ordre et de pause:

inst1 =ordreHeidi=> l , L =ordreHeidi_liste=>L1
____________________________________________________________           ,    ____________________________
inst1::pause::L =ordreHeidi_liste=>l::pause::L1                              [] =ordreHeidi_liste=> []

*/

//semantque ordreHeidi swift
//on evalue lordre de heidi pour tita
func evalOrdreHeidi (input: Term, output: Term) -> Goal {
  return
    (input === List.empty &&  output === List.empty)
    ||
    // --------------
    // deponer -evalOrdreHeidi-> court::court
    (input === deponer && output === List.cons(court, List.cons(court, List.empty)))
    ||
    //
    // --------------
    // dretg -evalOrdreHeidi-> whee::who
    (input === dretg && output === List.cons(whee, List.cons(who, List.empty)))
    ||
    //
    // --------------
    // sanester -evalOrdreHeidi-> wheet::wheeo
    (input === sanester && output === List.cons(wheet, List.cons(wheeo, List.empty)))
    ||
    //
    // --------------
    // davent -evalOrdreHeidi-> wheet::wheeo::wheet::wheet
    (input === davent && output === List.cons(wheet, List.cons(wheeo, List.cons(wheet, List.cons(wheet, List.empty)))))
    ||
    //
    // --------------
    // davos -evalOrdreHeidi-> who::hee::who
    (input === davos && output === List.cons(who, List.cons(hee, List.cons(who, List.empty))))
    ||
    //
    // --------------
    // plaun -evalOrdreHeidi-> hee::hee::hee::hee
    (input === plaun && output === List.cons(hee, List.cons(hee, List.cons(hee, List.cons(hee, List.empty)))))
    ||
    //
    // --------------
    // returnar -evalOrdreHeidi-> whee::whee::wheet
    (input === returnar && output === List.cons(whee, List.cons(whee, List.cons(wheet, List.empty))))
    ||
    //
    // --------------
    // safermar -evalOrdreHeidi-> long
    (input === safermar && output === List.cons(long, List.empty))
    ||
    // l -evalOrdreHeidi-> lv, r -evalOrdreHeidi->rv
    // _________________________________________
    // l::pause::r -evalOrdreHeidi-> lv::pause::rv
    delayed (freshn { g in
      let l  = g ["l"]
      let r  = g ["r"]
      let lv = g ["lv"]
      let rv = g ["rv"]
    return input === List.cons(l, List.cons(pause, r)) &&
             evalOrdreHeidi (input:l, output:lv) &&
             evalOrdreHeidi(input:r, output:rv) &&
             (output === List.cons(lv, List.cons(pause, rv)))


    })

}

//semantique d'un ordre de Tita regles d'inferences
/*
//on definit la syntaxe pour un ordre qui n'est  pas une liste:

___________________________         ,   _______________________________   ...
court::court =ordreTita=> deponer      whee::who=ordreTita=>   dretg

//on definit la syntaxe pour un ordre qui est une succession d'ordre et de pause:

inst1 =ordreTita=> l , L =ordreTita_liste=>L1
___________________________________________________________     ,    ______________________________
inst1::pause::L =ordreTita_liste=>l::pause::L1                         [] =ordreTita_liste=> []

inst === r::p::o ou bien inst === r::p::o::q ou bien inst === r::p ou bien inst === r
*/


//semantique swift pour ordreTita
//on evalue l'ordre de tita pour heidi
func evalOrdreTita (input: Term, output: Term) -> Goal {
  return
    (input === List.empty &&  output === List.empty)
    ||
    // --------------
    // court::court -evalOrdreTita-> deponer
    (input === List.cons(court, List.cons(court, List.empty)) && output === deponer)
    ||
    //
    // --------------
    // whee::who -evalOrdreTita-> dretg
    (input === List.cons(whee, List.cons(who, List.empty)) && output === dretg )
    ||
    //
    // --------------
    // wheet::wheeo -evalOrdreTita-> sanester
    (input === List.cons(wheet, List.cons(wheeo, List.empty)) && output === sanester)
    ||
    //
    // --------------
    // wheet::wheeo::wheet::wheet -evalOrdreTita-> davent
    (input === List.cons(wheet, List.cons(wheeo, List.cons(wheet, List.cons(wheet, List.empty)))) && output === davent)
    ||
    //
    // --------------
    // who::hee::who -evalOrdreTita-> davos
    (input === List.cons(who, List.cons(hee, List.cons(who, List.empty))) && output === davos)
    ||
    //
    // --------------
    // hee::hee::hee::hee -evalOrdreTita-> plaun
    (input === List.cons(hee, List.cons(hee, List.cons(hee, List.cons(hee, List.empty)))) && output === plaun)
    ||
    //
    // --------------
    // whee::whee::wheet -evalOrdreTita-> returnar
    (input === List.cons(whee, List.cons(whee, List.cons(wheet, List.empty))) && output === returnar)
    ||
    //
    // --------------
    // long -evalOrdreTita-> safermar
    (input === long && output === safermar)
    ||
    // l::r::o -evalOrdreTita-> q, p -evalOrdreTita->rv
    // _________________________________________
    // l::r::o pause p -evalOrdreTita-> q::pause::rv
    delayed (freshn { g in
      let l  = g ["l"]
      let r  = g ["r"]
      let o  = g ["o"]
      let p  = g ["p"]
      let q  = g ["q"]
      let rv = g ["rv"]
      return input === List.cons(l, List.cons(r, List.cons(o, List.cons(pause, p)))) &&
             evalOrdreTita (input:List.cons(l, List.cons(r, List.cons(o, List.empty))), output:q) &&
             evalOrdreTita(input:p, output:rv) &&
             (output === List.cons(q, List.cons(pause, rv)))

    })
    ||
    // l::r -evalOrdreTita-> q, p -evalOrdreTita->rv
    // _________________________________________
    // l::r::pause::p -evalOrdreTita-> q::pause::rv
    delayed (freshn { g in
      let l  = g ["l"]
      let r  = g ["r"]
      let p  = g ["p"]
      let q  = g ["q"]
      let rv = g ["rv"]
      return input === List.cons(l, List.cons(r, List.cons(pause, p))) &&
             evalOrdreTita (input:List.cons(l, List.cons(r, List.empty)), output:q) &&
             evalOrdreTita(input:p, output:rv) &&
             (output === List.cons(q, List.cons(pause, rv)))
    })
    ||
    // l::r::o::p -evalOrdreTita-> lv, q -evalOrdreTita->rv
    // _________________________________________
    // l::r::o::p::pause::q -evalOrdreTita-> lv::pause::rv)
    delayed (freshn { g in
      let l  = g ["l"]
      let r  = g ["r"]
      let o  = g ["o"]
      let p  = g ["p"]
      let q  = g ["q"]
      let lv = g ["lv"]
      let rv = g ["rv"]
      return input === List.cons(l, List.cons(r, List.cons(o, List.cons(p,List.cons(pause, q))))) &&
             evalOrdreTita (input:List.cons(l, List.cons(r, List.cons(o, List.cons(p,List.empty)))), output:lv) &&
             evalOrdreTita(input:q, output:rv) &&
             (output === List.cons(lv, List.cons(pause, rv)))
    })
    ||
    // l -evalOrdreTita-> lv, r -evalOrdreTita->rv
    // _________________________________________
    // l::pause::r -evalOrdreTita-> lv::pause::rv
    delayed (freshn { g in
      let l  = g ["l"]
      let r  = g ["r"]
      let lv = g ["lv"]
      let rv = g ["rv"]
    return input === List.cons(l, List.cons(pause, r)) &&
             evalOrdreTita(input:l, output:lv) &&
             evalOrdreTita(input:r, output:rv) &&
             (output === List.cons(lv, List.cons(pause, rv)))
    })


}
func traduction(input: Term, output: Term) -> Goal {
  return
    evalOrdreHeidi(input:input, output:output)
    ||
    evalOrdreTita(input:input, output:output)
  }

//optimisation

func evalOrdreHeidiOpt (input: Term, output: Term) -> Goal {
  return
    (input === List.empty &&  output === List.empty)
    ||
    // --------------
    // deponer -evalOrdreHeidiOpt-> wheeo::hee::wheet
    (input === deponer && output === List.cons(wheeo, List.cons(hee, List.cons(wheet, List.empty))))
    ||
    //
    // --------------
    // dretg -evalOrdreHeidiOpt-> hee::wheet
    (input === dretg && output === List.cons(hee, List.cons(wheet, List.empty)))
    ||
    //
    // --------------
    // sanester -evalOrdreHeidiOpt-> wheet::wheeo
    (input === sanester && output === List.cons(wheet, List.cons(wheeo, List.empty)))
    ||
    //
    // --------------
    // davent -evalOrdreHeidiOpt-> wheet::hee::wheet
    (input === davent && output === List.cons(wheet, List.cons(hee, List.cons(wheet, List.empty))))
    ||
    //
    // --------------
    // davos -evalOrdreHeidiOpt-> wheet::wheeo::wheet
    (input === davos && output === List.cons(wheet, List.cons(wheeo, List.cons(wheet, List.empty))))
    ||
    //
    // --------------
    // plaun -evalOrdreHeidiOpt-> wheet::wheeo::wheeo
    (input === plaun && output === List.cons(wheet, List.cons(wheeo, List.cons(wheeo, List.empty))))
    ||
    //
    // --------------
    // returnar -evalOrdreHeidiOpt-> wheeo::wheet
    (input === returnar && output === List.cons(wheeo, List.cons(wheet, List.empty)))
    ||
    //
    // --------------
    // safermar -evalOrdreHeidiOpt-> wheeo::wheeo
    (input === safermar && output === List.cons(wheeo, List.cons(wheeo, List.empty)))
    ||
    // l -evalOrdreHeidiOpt-> lv, r -evalOrdreHeidiOpt->rv
    // _________________________________________
    // l::pause::r -evalOrdreHeidiOpt-> lv::pause::rv
    delayed (freshn { g in
      let l  = g ["l"]
      let r  = g ["r"]
      let lv = g ["lv"]
      let rv = g ["rv"]
    return input === List.cons(l, List.cons(pause, r)) &&
             evalOrdreHeidiOpt (input:l, output:lv) &&
             evalOrdreHeidiOpt(input:r, output:rv) &&
             (output === List.cons(lv, List.cons(pause, rv)))


    })

}

//optimisation semantque du langage de Tita

func evalOrdreTitaOpt (input: Term, output: Term) -> Goal {
  return
    (input === List.empty &&  output === List.empty)
    ||
    // --------------
    // wheeo::hee::wheet -evalOrdreTitaOpt-> deponer
    (input === List.cons(wheeo, List.cons(hee, List.cons(wheet, List.empty))) && output === deponer)
    ||
    //
    // --------------
    // hee::wheet -evalOrdreTitaOpt-> dretg
    (input === List.cons(hee, List.cons(wheet, List.empty)) && output === dretg)
    ||
    //
    // --------------
    // wheet::wheeo -evalOrdreTitaOpt-> sanester
    (input === List.cons(wheet, List.cons(wheeo, List.empty)) && output === sanester)
    ||
    //
    // --------------
    // wheet::hee::wheet -evalOrdreTitaOpt-> davent
    (input === List.cons(wheet, List.cons(hee, List.cons(wheet, List.empty))) && output === davent)
    ||
    //
    // --------------
    // wheet::wheeo::wheet-evalOrdreTitaOpt-> davos
    (input === List.cons(wheet, List.cons(wheeo, List.cons(wheet, List.empty))) && output === davos)
    ||
    //
    // --------------
    // wheet::wheeo::wheeo-evalOrdreTitaOpt-> plaun
    (input === List.cons(wheet, List.cons(wheeo, List.cons(wheeo, List.empty))) && output === plaun)
    ||
    //
    // --------------
    // wheeo::wheet -evalOrdreTitaOpt-> returnar
    (input === List.cons(wheeo, List.cons(wheet, List.empty)) && output === returnar)
    ||
    //
    // --------------
    // wheeo::wheeo -evalOrdreTitaOpt-> safermar
    (input === List.cons(wheeo, List.cons(wheeo, List.empty)) && output === safermar)
    ||
    // l::r::o -evalOrdreTitaOpt-> q, p -evalOrdreTita->rv
    // _________________________________________
    // l::r::o pause p -evalOrdreTitaOpt-> q::pause::rv
    delayed (freshn { g in
      let l  = g ["l"]
      let r  = g ["r"]
      let o  = g ["o"]
      let p  = g ["p"]
      let q  = g ["q"]
      let rv = g ["rv"]
      return input === List.cons(l, List.cons(r, List.cons(o, List.cons(pause, p)))) &&
             evalOrdreTitaOpt (input:List.cons(l, List.cons(r, List.cons(o, List.empty))), output:q) &&
             evalOrdreTitaOpt(input:p, output:rv) &&
             (output === List.cons(q, List.cons(pause, rv)))
    })
    ||
    // l::r -evalOrdreTitaOpt-> q, p -evalOrdreTitaOpt->rv
    // _________________________________________
    // l::r::pause::p -evalOrdreTitaOpt-> q::pause::rv
    delayed (freshn { g in
      let l  = g ["l"]
      let r  = g ["r"]
      let p  = g ["p"]
      let q  = g ["q"]
      let rv = g ["rv"]
      return input === List.cons(l, List.cons(r, List.cons(pause, p))) &&
             evalOrdreTitaOpt (input:List.cons(l, List.cons(r, List.empty)), output:q) &&
             evalOrdreTitaOpt(input:p, output:rv) &&
             (output === List.cons(q, List.cons(pause, rv)))
    })

}

//preuve que la traduction romanche_siflet_romanche retourne la texte d'origine
/*
-si l'ordre donné par heidi est un mot m simple c'est-à-dire n'est pas une liste, on verifie facilement qu'on a :
m =evalOrdreHeidi=> m' =evalOrdreTita= m (exemple d'apres evalOrdreHeidi on a  "deponer =evalOrdreHeidi=> List.cons(court, List.cons(court, List.empty))"
et d'apres evalOrdreTita, on a aussi List.cons(court, List.cons(court, List.empty)) =evalOrdreTita=> deponer)

-si l'ordre est une liste . On sait que la traduction se fait element par element , donc si l'évaluation
"élément =evalOrdreHeidi=> element1 =evalOrdreTita=> élément" est verifiée, elle l'est pour toute la liste.

voici une petite illustration : si l'ordre de heidi est : L = m::pause::m1::pause::m2::pause::m3....pause::mx
alors on a  : L =evalOrdreHeidi=> m'::pause::evalOrdreHeidi (m1::m2::m3....pause::mx) avec m =evalOrdreHeidi=> m' etc.
on aura donc L =evalOrdreHeidi=> m'::pause::m1'::pause::m2'::pause::m3'...pause::mx'
et  m'::pause::m1'::pause::m2'::pause::m3' ...pause::mx' =evalOrdreTita=> m ::pause::evalOrdreTita(m1'::pause::m2'::pause::m3'...pause::mx') etc.
finalement on a : m::pause::m1::pause::m2::pause::m3...pause::mx =evalOrdreHeidi=> m'::pause::evalOrdreHeidi (m1::m2::m3..pause::mx) =evalOrdreTita=> m ::pause::evalOrdreTita(m1'::pause::m2'::pause::m3'...pause::mx')
de meme pour chaque element de la liste par conjecture on a la liste de depart qui se reforme.

*/

//acceleration
