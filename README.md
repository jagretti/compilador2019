Compiladores
========================================

Bienvenide!

El código proporcionado en este repo es un esqueleto básico para el desarrollo
de la materia de Compiladores de Lcc. En general se trató de ser lo más prolijo
posible, dejando además lugar (y libertad) al estudiante que esté dispuesto a
jugar un poco más con ML y Tiger.

En principio lo ideal es que le estudiante pueda tomar las decisiones que quiera
y seguir tanto como quiera al esqueleto como realizar las modificaciones
necesarias a gusto.

Como sabrán seguiremos el
[libro](https://www.cs.princeton.edu/~appel/modern/ml/) de Andrew Appel quien a
su vez ya otorga bastante código que pueden encontrar en el link del libro. En
principio el código que encontrarán en el repositorio es el *mismo* aunque con
más código.

Voy a remarcar una vez más que pueden implementar el compilador en el lenguaje
de su preferencia, aunque mi recomendación es que tenga un uso sencillo de
estructuras y particularmente *pattern matching*.

En este repositorio encontrarán el esqueleto para realizarlo en SML, aunque hay
otro repositorio donde encontrarán un esqueleto (ya sin soporte) en
[Haskell](https://git.dcc.fceia.unr.edu.ar/Compiladores)

Verán que se encuentra divido en 3 entregas, esta división es una decisión
didáctica y práctica, para ir poniendo metas intermedias aunque no necesarias.
+ Entrega 1: Análisis Semántico.
  La primer etapa se centra en el *Análisis Semántico*, es decir, en el 
  análisis de tipos del código fuente. Aquí la gran dificultad estará en la
  detección de ciclos dentro de los tipos de datos mutuamente recursivos, aunque
  deberán permitir dichos ciclos dentro de los Records.
+ Entrega 2: Generación de Código Intermedio.
  La segunda etapa consistirá principalmente en la generación de código
  intermedio, es decir, deberán traducir (o simplificar) el AST a un lenguaje
  mucho más cercano a un lenguaje ensamblador aunque todavía lo suficiente
  general que nos permita abstraer la arquitectura objeto.
+ Entrega 3: Selección de Instrucciones y Alocación de Registros.
  Finalmente, deberán especificar como traducir del código intermedio a la(s)
  instrucción(es) de la arquitectura que elijan, para proceder a terminar con la
  fantasía de infinitos registros (temporales) y tener que decidir cuantos
  registros hay en realidad.
  
Estructura general (Appel Fig 1.1) :

Las etapas entre llaves ({}) son las que deberán implementar ustedes.

|  Source Program                   |
>>  Lex                            >>
|  Tokens                           |
>>  Parse                          >>
|  Reductions                       |
>>  Parsing Actions                >>
|  AST                              |
>>  {Semantic Analysis with Tables}>>
|  Translate                        |
>>{Translate with Frame Generation}>>
|  IR Trees                         |
>>  Canonicalize                   >>
|  IR Trees                         |
>>  {IntructionSelection}          >>
|  Assem                            |
>>  {Control Flow Analysis}         >>
|  Flow Graph                       |
>>  {Data Flow Analysis}           >>
|  Inference Graph                  |
>>  {Register Allocation}          >>
|  Register Assignment              |
>>  {Code Emission}                >>
|  Assembly Language                |
>>  Assembler                      >>
|  Relocatable Object Code          |
>>  Linker                         >>
|  Machine Language                 |

  
Descripción General de los Archivos:
----------------------------------------
Archivos relacionados a etapas del compilador.

Entrega 1:

+ [TigerLexer](entrega1/tigerlex.lex)/ [TigerGrammar](entrega1/tigergrm.s): Analizador lexicográfico, gramática y parser (**gratis**), `text -> exp`.
+ [TigerEscap](entrega1/tigerescap.sig): Cálculo de variables escapadas(**gratis**), `Exp -> Exp`.
+ [TigerSeman](entrega1/tigerseman.sig): Análisis Semántico, inferidor de tipos, `Exp -> Exp`.
+ [TigerAbs](entrega1/tigerabs.sml): Contiene la estructura `Exp`.
+ [TigerPP](entrega1/tigerpp.sig): PP de código fuente.
+ [TigerTip](entrega1/tigertip.sml): Estructura de los tipos de Tiger.
+ [TigerSres](entrega1/tigersres.sml): Representación de valores/funciones en las tabla de entornos, útiles para las primeras etapas.

Entrega 2:

+ [TigerTrans](entrega2/tigertrans.sig): Generador de código intermedio, `Exp -> Stm`.
+ [TigerCanon](entrega2/tigercanon.sig): Canonizador de código intermedio(**gratis**), `Stm -> [Stm]`.
+ [TigerTree](entrega2/tigertree.sml): Contiene la estructura de código intermedio `Stm`.
+ [TigerFrame](entrega2/tigerframe.sig): Abstracción de la arquitectura a elegir.
+ [TigerInterp](entrega2/tigertnterp.sml): Interprete de código intermedio, extremadamente útil para debuggear al terminar esta etapa.

Entrega 3:
+ [Runtime](entrega3/runtime.c): Runtime escrito en C.
+ [TigerAssem](entrega3/tigerassem.sml): Representación de Instrucciones de ensamblador.

NOTA: Faltan archivos relacionados a las *últimas etapas*, o a la ultima etapa. Ya son grandes
deberían poder manejarse solitos.
