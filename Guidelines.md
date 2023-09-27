Following are guidelines that one should follow unless there is a good technical reason not to.

* Languages features to avoid:
    * import opened.
    * subset and new types.
    * covariance and contraviance.
    * Induction-recursion datatypes.

* Even if a function is not meant to be part of the compiled code, don't use ghost unless necessary.
* Do not attach postconditions to functions. Instead, prove the postcondition as a separate lemma.
* Make functions opaque.
* Name preconditions of lemmas and reveal them only when necessary.
* Be mindful of resource usage and refine your proof until it is less than 1M.
* In particular, avoid `{:vcs_split_on_every_assert}` as this can increase the verification time a lot.
* Keep proofs short and modular, as for a pencil and paper proof.
* Prefer structured proofs in natural deduction rathen than sequences of assertions.
* Unless it is logically or mathematically necessary:
<table>
   <tr>
      <td> Instead of... </td> <td> Do... </td>
   </tr>
   <tr> </tr>
   <tr>
      <td>
<pre>
lemma Foo()
  ensures forall x: nat :: P(x)
</pre>
      </td>
      <td>
<pre>
lemma Foo(x:nat)
  ensures P(x)
</pre>
      </td>
   </tr>
   <tr> </tr>
   <tr>
      <td>
<pre>
lemma Foo()
  ensures A ==> B
</pre>
      </td>
      <td>
<pre>
lemma Foo()
  requires A
  ensures B
</pre>
      </td>
   </tr>
   <tr> </tr>
   <tr>
      <td>
<pre>
lemma Foo()
  ensures A /\ B
</pre>
      </td>
      <td>
<pre>
lemma Foo1()
  ensures A
<br>
lemma Foo2()
  ensures B
</pre>
      </td>
   </tr>
   <tr> </tr>
   <tr>
      <td>
<pre>
lemma Foo()
  ensures A <==> B
</pre>
      </td>
      <td>
<pre>
lemma Foo1()
  requires A
  ensures B
<br>
lemma Foo2()
  requires B
  ensures A
</pre>
      </td>
   </tr>
   <tr> </tr>
   <tr>
      <td>
<pre>
lemma Foo()
  ensures exists x: T :: P(x)
</pre>
      </td>
      <td>
<pre>
lemma Foo() returns (x: T)
  ensures P(x)
</pre>
      </td>
   </tr>
   <tr> </tr>
   <tr>
      <td>
<pre>
lemma Foo()
  requires A /\ B
  ensures C
</pre>
      </td>
      <td>
<pre>
lemma Foo()
  requires A
  requires B
  ensures C
</pre>
      </td>
   </tr>
   <tr> </tr>
   <tr>
      <td>
<pre>
lemma Foo()
  requires A \/ B
  ensures C
</pre>
      </td>
      <td>
<pre>
lemma Foo1()
  requires A
  ensures C
   <br>
lemma Foo2()
  requires B
  ensures C
</pre>
      </td>
   </tr>
</table>
* Establish preconditions of assertion in a by clause. For example, consider lemma Foo() requires A ensures B
<table>
   <tr>
      <td> Instead of... </td> <td> Do... </td>
   </tr>
   <tr> </tr>
   <tr>
      <td>
<pre>
assert A;
Foo();
</pre>
      </td>
      <td>
<pre>
assert B by {
  assert A;
  Foo();
}
</pre>
      </td>
   </tr>
</table>












