--- before_pass
+++ after_pass
@@ -30,7 +30,7 @@ control cIngress(inout headers_t hdr, in
         meta_1.egress_port = egress_port_1;
         ostd = meta_1;
     }
-    @name("cIngress.counter") Counter<bit<10>, bit<12>>(32w1024, PSA_CounterType_t.PACKETS) counter_0;
+    @name("cIngress.counter") Counter<bit<10>, bit<12>>(32w1024, 32w0) counter_0;
     @name("cIngress.execute") action execute_1() {
         counter_0.count(12w256);
     }
