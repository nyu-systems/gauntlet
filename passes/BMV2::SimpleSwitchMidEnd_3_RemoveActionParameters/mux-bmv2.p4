--- dumps/pruned/mux-bmv2-BMV2::SimpleSwitchMidEnd_2_EliminateSerEnums.p4	2019-06-08 18:32:58.182100600 +0200
+++ dumps/pruned/mux-bmv2-BMV2::SimpleSwitchMidEnd_3_RemoveActionParameters.p4	2019-06-08 18:32:58.212789300 +0200
@@ -17,7 +17,11 @@ control Eg(inout Headers hdrs, inout Met
     bit<32> _sub;
     bit<64> res;
     bit<32> tmp_0;
-    @name("Eg.update") action update_0(in bool p_1, inout bit<64> val) {
+    bool p_1;
+    bit<64> val;
+    @name("Eg.update") action update_0() {
+        p_1 = true;
+        val = res;
         _sub = val[31:0];
         if (p_1) 
             tmp_0 = _sub;
@@ -25,10 +29,11 @@ control Eg(inout Headers hdrs, inout Met
             tmp_0 = 32w1;
         _sub = tmp_0;
         val[31:0] = _sub;
+        res = val;
     }
     apply {
         res = 64w0;
-        update_0(true, res);
+        update_0();
     }
 }
 control DP(packet_out b, in Headers p) {
