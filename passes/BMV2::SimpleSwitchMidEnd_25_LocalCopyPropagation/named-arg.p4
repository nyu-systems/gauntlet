--- dumps/pruned/named-arg-BMV2::SimpleSwitchMidEnd_24_ConstantFolding.p4	2019-06-08 18:32:58.610208400 +0200
+++ dumps/pruned/named-arg-BMV2::SimpleSwitchMidEnd_25_LocalCopyPropagation.p4	2019-06-08 18:32:58.614799500 +0200
@@ -1,11 +1,7 @@
 extern void f(in bit<16> x, in bool y);
 control c() {
-    bit<16> xv;
-    bool b;
     apply {
-        xv = 16w0;
-        b = true;
-        f(x = xv, y = b);
+        f(x = 16w0, y = true);
     }
 }
 control empty();
