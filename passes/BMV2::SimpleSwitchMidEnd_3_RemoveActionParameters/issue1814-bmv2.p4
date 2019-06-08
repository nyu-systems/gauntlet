--- before_pass
+++ after_pass
@@ -11,9 +11,9 @@ parser ParserImpl(packet_in packet, out
     }
 }
 control IngressImpl(inout headers hdr, inout metadata meta, inout standard_metadata_t standard_metadata) {
+    bit<1> registerData;
     @name(".NoAction") action NoAction_0() {
     }
-    bit<1> registerData;
     @name("IngressImpl.testRegister") register<bit<1>>(32w1) testRegister;
     @name("IngressImpl.debug_table") table debug_table {
         key = {
