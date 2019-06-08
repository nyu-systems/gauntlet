--- before_pass
+++ after_pass
@@ -3,12 +3,6 @@ struct S {
 }
 control c(inout bit<32> b) {
     @name("c.a") action a_0() {
-        {
-        }
-        {
-        }
-        {
-        }
         b = 32w0;
     }
     apply {
