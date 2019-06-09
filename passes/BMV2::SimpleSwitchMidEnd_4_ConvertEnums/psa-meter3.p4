--- before_pass
+++ after_pass
@@ -24,7 +24,7 @@ control MyIC(inout ethernet_t a, inout E
     bool tmp_0;
     @name(".NoAction") action NoAction_0() {
     }
-    @name("MyIC.meter0") Meter<bit<12>>(32w1024, PSA_MeterType_t.PACKETS) meter0_0;
+    @name("MyIC.meter0") Meter<bit<12>>(32w1024, 32w0) meter0_0;
     @name("MyIC.tbl") table tbl_0 {
         key = {
             a.srcAddr: exact @name("a.srcAddr") ;
@@ -36,7 +36,7 @@ control MyIC(inout ethernet_t a, inout E
     }
     apply {
         tmp = meter0_0.execute(12w0);
-        tmp_0 = tmp == PSA_MeterColor_t.GREEN;
+        tmp_0 = tmp == 32w1;
         if (tmp_0) 
             tbl_0.apply();
     }
