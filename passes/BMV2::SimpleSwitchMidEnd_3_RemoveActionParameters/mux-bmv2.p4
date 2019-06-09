--- before_pass
+++ after_pass
@@ -17,7 +17,11 @@ control Eg(inout Headers hdrs, inout Met
     bit<32> _sub_0;
     bit<64> res_0;
     bit<32> tmp;
-    @name("Eg.update") action update(in bool p_1, inout bit<64> val) {
+    bool p_1;
+    bit<64> val;
+    @name("Eg.update") action update() {
+        p_1 = true;
+        val = res_0;
         _sub_0 = val[31:0];
         if (p_1) 
             tmp = _sub_0;
@@ -25,10 +29,11 @@ control Eg(inout Headers hdrs, inout Met
             tmp = 32w1;
         _sub_0 = tmp;
         val[31:0] = _sub_0;
+        res_0 = val;
     }
     apply {
         res_0 = 64w0;
-        update(true, res_0);
+        update();
     }
 }
 control DP(packet_out b, in Headers p) {
