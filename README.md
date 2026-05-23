# Práctica 11: Introducción a Rocq (Lógica Computacional 2026-2)

**Integrantes:**
- Joaquin Rodrigo Ramirez Mendoza
- Dana Ximena Sanchez Loaeza

---

## Bloque 1: Tipos, Check y Compute

Al ejecutar `Check` en jsCoq obtuvimos:

- `Check true.`  ⇒ `true : bool`
- `Check false.` ⇒ `false : bool`
- `Check negb.`  ⇒ `negb : bool -> bool`
- `Check (negb true).` ⇒ `negb true : bool`
- `Check nat.` ⇒ `nat : Set`
- `Check (S (S O)).` ⇒ `2 : nat`
- `Check (1 + 1 = 2).` ⇒ `1 + 1 = 2 : Prop`
- `Check (forall n : nat, n = n).` ⇒ `forall n : nat, n = n : Prop`

`Check` no evalúa; solo reporta el **tipo**. Se observa que:
- Los booleanos viven en el tipo `bool`.
- `negb` es una función `bool -> bool`.
- `nat` pertenece a `Set` (que es un tipo de datos).
- Igualdades como `1 + 1 = 2` y cuantificaciones como `forall n, n = n` son proposiciones en `Prop`.

### Resultados de `Compute`

Al ejecutar `Compute` en jsCoq obtuvimos:

- `Compute negb (negb true).` ⇒ `= true : bool`
- `Compute andb true false.` ⇒ `= false : bool`
- `Compute orb false false.` ⇒ `= false : bool`
- `Compute 3 + 4.` ⇒ `= 7 : nat`
- `Compute 10 - 3.` ⇒ `= 7 : nat`
- `Compute 10 - 15.` ⇒ `= 0 : nat`
- `Compute 2 * 6.` ⇒ `= 12 : nat`

**Interpretación:**  
`Compute` reduce definiciones y calcula resultados concretos. En particular, se confirma que la resta en `nat` es **truncada**: `10 - 15` devuelve `0` porque no existen naturales negativos.

### Diferencia entre `Check` y `Compute`
- `Check` **no evalúa** expresiones: únicamente **verifica e imprime el tipo** (o la proposición) de lo que escribimos. Sirve para inspeccionar qué “clase” de cosa es un término (por ejemplo, que `negb` es una función `bool -> bool`, o que `forall n:nat, n=n` es una proposición).
- `Compute` sí **evalúa/reduce** una expresión hasta una forma normal (según las definiciones) y nos muestra el resultado concreto.

### Sobre la resta `10 - 15` en `nat`
En `nat` (naturales de Peano), la resta está **truncada**: no existen números negativos.  
Por eso, cuando restamos “más de lo que hay”, el resultado se **satura en 0**:
- `Compute 10 - 3` da `7`
- `Compute 10 - 15` da `0` (porque no puede dar `-5`)

---

## Bloque 2: Definiciones y `Fixpoint`

### Terminación de la función `pot`
Rocq acepta la terminación porque `pot` está definida por **recursión estructural** sobre el exponente `e`:

```coq
Fixpoint pot (b e : nat) : nat :=
  match e with
  | O => S O
  | S e' => mult_nat b (pot b e')
  end.
```

En cada llamada recursiva, el argumento `e` disminuye de `S e'` a `e'`, es decir, Rocq puede verificar que siempre se acerca a `O`. Por eso no protesta por terminación.

Además, en las funciones aritméticas del bloque (`suma_nat`, `mult_nat`, `pot`) evitamos `+` y `*` predefinidos: todo se construye con `O`, `S` y `match`, como pide la práctica.

---

## Bloque 4: Análisis por casos con `destruct`

### Casos generados por `destruct` anidado
- **Sobre dos `bool`:** `2 × 2 = 4` casos (porque `bool` solo tiene `true` y `false`).
- **Sobre dos `nat`:** un `destruct` separa en `O` y `S n'`.  
  Si anidamos `destruct` sobre dos `nat` obtenemos `2 × 2 = 4` formas iniciales:  
  `(O,O)`, `(O,S m')`, `(S n',O)`, `(S n', S m')`.

### ¿Es razonable para naturales?
Para algunas propiedades sobre `nat`, `destruct` basta si la definición ya “reduce” suficiente.

En esta práctica, `par_S_impar` se puede resolver con `destruct` porque `par` reduce dos pasos a la vez (`par (S (S k)) = par k`), así que al separar `n` en los casos `0`, `1` y `S (S k)` el objetivo se cierra por `simpl; reflexivity`.

En cambio, hay propiedades como `compara_refl` donde el caso `S n'` reduce al mismo enunciado para `n'`, y ahí sí sería natural usar inducción.

---

## Bloque 6: `Admitted` y `Abort`

### ¿Qué advertencia da Rocq al usar `Admitted`?
Rocq acepta el teorema **sin comprobación formal**. Esto deja una advertencia (por ejemplo, “There are admitted goals” o “Using Admitted”) indicando que el desarrollo contiene un resultado **no probado**: en la práctica, se introduce como un “axioma” local.

### ¿Cuándo conviene usar `Admitted` y cuándo `Abort`?
- **`Admitted`**: conviene cuando quieres **seguir compilando y avanzando** aunque falte la demostración, y necesitas usar el teorema después (por ejemplo con `rewrite`). En nuestro código, `usa_admitted` reescribe dos veces usando `ejemplo_admitted`.
- **`Abort`**: conviene cuando el teorema fue un **intento exploratorio** o incorrecto y no quieres que quede registrado. Con `Abort` el teorema **no existe** al final, así que no puede usarse más adelante.

### Riesgos de usar `Admitted` en desarrollos grandes
Deja “agujeros” en la verificación: si un lema admitido fuera falso, entonces cualquier prueba que dependa de él (directa o indirectamente) puede ser inválida aunque Rocq la acepte. En proyectos grandes, esto puede contaminar muchas partes del desarrollo y dar una falsa sensación de corrección.

---

## Bloque 7: Reto final

### Reflexión sobre `compara_refl`
El teorema es:

```coq
forall n : nat, compara n n = Eq
```

Al hacer `destruct n`, el caso `n = O` se resuelve por `simpl; reflexivity`, pero el caso `n = S n'` se reduce a demostrar:

```coq
compara n' n' = Eq
```

que es el **mismo enunciado** para un `n'` más pequeño. Para cerrar ese patrón “para todo n” hace falta la táctica `induction` (inducción estructural), pero aquí se dejó con `Admitted`.

**¿Qué ocurre en el entorno al cerrarlo con `Admitted`?**  
`compara_refl` queda disponible como si fuera cierto (igual que un axioma local). Eso permite usarlo en reescrituras o pruebas posteriores, pero ya no tenemos la garantía de que el resultado esté formalmente verificado.