--- before_pass
+++ after_pass
@@ -1,4 +1,5 @@
 control d(out bit<32> x) {
+    bool cinst_hasReturned;
     @name("d.cinst.a1") action cinst_a1_0() {
     }
     @name("d.cinst.a2") action cinst_a2_0() {
@@ -12,7 +13,7 @@ control d(out bit<32> x) {
     }
     apply {
         {
-            bool cinst_hasReturned = false;
+            cinst_hasReturned = false;
             switch (cinst_t.apply().action_run) {
                 cinst_a1_0: 
                 cinst_a2_0: {
