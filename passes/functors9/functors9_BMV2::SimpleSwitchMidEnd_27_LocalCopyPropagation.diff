--- before_pass
+++ after_pass
@@ -6,10 +6,9 @@ extern e<T> {
 parser simple(in bit<2> a);
 package m(simple n);
 parser p1_0(in bit<2> a) {
-    bit<2> tmp;
     @name("p1_0.ei") e<bit<2>>() ei_0;
     state start {
-        tmp = ei_0.get();
+        ei_0.get();
         transition accept;
     }
 }
