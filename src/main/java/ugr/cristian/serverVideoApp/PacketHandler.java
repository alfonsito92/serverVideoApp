/**
Copyright (C) 2015  Cristian Alfonso Prieto Sánchez

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
GNU General Public License for more details.

You should have getTransmitErrorCountd a copy of the GNU General Public License
along with this program. If not, see <http://www.gnu.org/licenses/>.
*/

package ugr.cristian.serverVideoApp;

/**
*@author Cristian Alfonso Prieto Sánchez
*/

import java.lang.System;
import java.util.concurrent.Semaphore;

import java.net.InetAddress;
import java.net.UnknownHostException;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;
import java.util.Iterator;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ConcurrentMap;
import java.util.Map;
import java.util.HashMap;
import java.util.Set;
import java.util.HashSet;

import org.opendaylight.controller.sal.action.Action;
import org.opendaylight.controller.sal.action.Controller;
import org.opendaylight.controller.sal.action.Output;
import org.opendaylight.controller.sal.action.SetDlDst;
import org.opendaylight.controller.sal.action.SetDlSrc;
import org.opendaylight.controller.sal.action.SetNwDst;
import org.opendaylight.controller.sal.action.SetNwSrc;
import org.opendaylight.controller.sal.core.ConstructionException;
import org.opendaylight.controller.sal.core.Bandwidth;
import org.opendaylight.controller.sal.core.Node;
import org.opendaylight.controller.sal.core.Edge;
import org.opendaylight.controller.sal.core.Host;
import org.opendaylight.controller.sal.core.Latency;
import org.opendaylight.controller.sal.core.Property;
import org.opendaylight.controller.sal.core.Path;
import org.opendaylight.controller.sal.core.NodeConnector;
import org.opendaylight.controller.sal.flowprogrammer.Flow;
import org.opendaylight.controller.sal.flowprogrammer.IFlowProgrammerService;
import org.opendaylight.controller.sal.match.Match;
import org.opendaylight.controller.sal.match.MatchType;
import org.opendaylight.controller.sal.packet.BitBufferHelper;
import org.opendaylight.controller.sal.packet.Ethernet;
import org.opendaylight.controller.sal.packet.IDataPacketService;
import org.opendaylight.controller.sal.packet.IListenDataPacket;
import org.opendaylight.controller.sal.packet.IPv4;
import org.opendaylight.controller.sal.packet.ICMP;
import org.opendaylight.controller.sal.packet.TCP;
import org.opendaylight.controller.sal.packet.UDP;
import org.opendaylight.controller.sal.packet.Packet;
import org.opendaylight.controller.sal.packet.PacketResult;
import org.opendaylight.controller.sal.packet.RawPacket;
import org.opendaylight.controller.sal.reader.FlowOnNode;
import org.opendaylight.controller.sal.reader.NodeConnectorStatistics;
import org.opendaylight.controller.sal.utils.IPProtocols;
import org.opendaylight.controller.sal.utils.Status;
import org.opendaylight.controller.switchmanager.ISwitchManager;
import org.opendaylight.controller.topologymanager.ITopologyManager;
import org.opendaylight.controller.statisticsmanager.IStatisticsManager;

import edu.uci.ics.jung.algorithms.shortestpath.DijkstraShortestPath;
import edu.uci.ics.jung.graph.Graph;
import edu.uci.ics.jung.graph.SparseMultigraph;
import edu.uci.ics.jung.graph.util.EdgeType;

import org.apache.commons.collections15.Transformer;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class PacketHandler implements IListenDataPacket {

  private static final Logger log = LoggerFactory.getLogger(PacketHandler.class);

  private IDataPacketService dataPacketService;
  private ISwitchManager switchManager;
  private IFlowProgrammerService flowProgrammerService;
  private IStatisticsManager statisticsManager;
  private ITopologyManager topologyManager;

  private ConcurrentMap<Map<Node, InetAddress>, NodeConnector> tableIP = new ConcurrentHashMap<Map<Node, InetAddress>, NodeConnector>();
  private Map<Node, Set<Edge>> nodeEdges = new HashMap<Node, Set<Edge>>();

  private ConcurrentMap<Map<Node, Node>, List<Edge>> rtpPathMap = new ConcurrentHashMap<Map<Node, Node>, List<Edge>>();

  private ConcurrentMap<Map<Node, Node>, List<Edge>> icmpPathMap = new ConcurrentHashMap<Map<Node, Node>, List<Edge>>();

  private Edge edgeMatrix[][];

  private Long latencyMatrix[][];
  private Long minLatency;
  private Long mediumLatencyMatrix[][];
  private Long minMediumLatency;

  private Map<Edge, Set<Packet>> edgePackets = new HashMap<Edge, Set<Packet>>();
  private ConcurrentMap<Map<Edge, Packet>, Long> packetTime = new ConcurrentHashMap<Map<Edge, Packet>, Long>();

  private Long standardCostMatrix[][];
  private Long rtpCostMatrix[][];

  private ConcurrentMap<Edge, Map<String, ArrayList>> edgeStatistics = new ConcurrentHashMap<Edge, Map<String, ArrayList>>();
  private Map<String, Long> maxStatistics = new HashMap<String, Long>();

  private Map<Edge, Long> edgeCostMap = new HashMap<Edge, Long>();
  private Map<Edge, Long> rtpEdgeCostMap = new HashMap<Edge, Long>();


  private Transformer<Edge, ? extends Number> costTransformer = null;
  private Transformer<Edge, ? extends Number> costRTPTransformer = null;

  private Graph<Node, Edge> g = new SparseMultigraph();

  private DijkstraShortestPath<Node, Edge> standardShortestPath;
  private DijkstraShortestPath<Node, Edge> rtpShortestPath;

  private Map<Edge, ArrayList> edgeMediumMapTime = new HashMap<Edge, ArrayList>();

  private short idleTimeOut = 20;
  private short hardTimeOut = 30;

  private Map<Node, Set<Packet>> receivedPackets = new HashMap<Node, Set<Packet>>();

  /*********Statistics Constants**********/

  private final String transmitBytes = "Transmits Bytes";
  private final String receiveBytes = "Receive Bytes";
  private final String transmitDropBytes = "Transmit Drop Bytes";
  private final String receiveDropBytes = "Receive Drop Bytes";
  private final String transmitErrorBytes = "Transmit Error Bytes";
  private final String receiveErrorBytes = "Receive Error Bytes";
  private final String[] statisticsName = {transmitBytes, receiveBytes, transmitDropBytes,
  receiveDropBytes, transmitErrorBytes, receiveErrorBytes};

  /***************************************/

  /*************************************/
  private final Long defaultCost = 5L; //If we don't have any latency measure

  private int flood = 0;

  private int MAXFLOODPACKET = 5;

  private final Integer rtpPort = 5004;
  private final String RTPSTRING = "10000000";
  private final Long RTPFACTOR = 1000L; //To get the difference in ms
  private final Long RTPDEFAULTCOST = 30L;

  private final Integer audioPort = 2543;

  /*************************************/
  private final Integer MAXPACKETCOUNTER = 5;
  private Integer counter = 5;
  /*************************************/

  /*************************************/
  static final Semaphore semaforo=new Semaphore(1);
  static final Semaphore delFlowSemaforo = new Semaphore(1);
  /************************************/

  static private InetAddress intToInetAddress(int i) {
    byte b[] = new byte[] { (byte) ((i>>24)&0xff), (byte) ((i>>16)&0xff), (byte) ((i>>8)&0xff), (byte) (i&0xff) };
    InetAddress addr;
    try {
        addr = InetAddress.getByAddress(b);
    } catch (UnknownHostException e) {
        return null;
    }

    return addr;
  }

    /**
     * Sets a reference to the requested DataPacketService
     */
    void setDataPacketService(IDataPacketService s) {
        log.trace("Set DataPacketService.");

        dataPacketService = s;
    }

    /**
     * Unsets DataPacketService
     */
    void unsetDataPacketService(IDataPacketService s) {
        log.trace("Removed DataPacketService.");

        if (dataPacketService == s) {
            dataPacketService = null;
        }
    }

    /**
     * Sets a reference to the requested SwitchManagerService
     */
    void setSwitchManagerService(ISwitchManager s) {
        log.trace("Set SwitchManagerService.");

        switchManager = s;
    }

    /**
     * Unsets SwitchManagerService
     */
    void unsetSwitchManagerService(ISwitchManager s) {
        log.trace("Removed SwitchManagerService.");

        if (switchManager == s) {
            switchManager = null;
        }
    }

    /**
     * Sets a reference to the requested FlowProgrammerService
     */
    void setFlowProgrammerService(IFlowProgrammerService s) {
        log.trace("Set FlowProgrammerService.");

        flowProgrammerService = s;
    }

    /**
     * Unsets FlowProgrammerService
     */
    void unsetFlowProgrammerService(IFlowProgrammerService s) {
        log.trace("Removed FlowProgrammerService.");

        if (flowProgrammerService == s) {
            flowProgrammerService = null;
        }
    }

    /**
     * Sets a reference to the requested StatisticsService
     */
    void setStatisticsManagerService(IStatisticsManager s) {
        log.trace("Set StatisticsManagerService.");

        statisticsManager = s;
    }

    /**
     * Unset StatisticsManager
     */
    void unsetStatisticsManagerService(IStatisticsManager s) {
        log.trace("Unset StatisticsManagerService.");

        if (  statisticsManager == s) {
            statisticsManager = null;
        }
    }

    /**
     * Sets a reference to the requested TopologyManager
     */
    void setTopologyManagerService(ITopologyManager s) {
        log.trace("Set TopologyManagerService.");

        topologyManager = s;
    }

    /**
     * Unset TopologyManager
     */
    void unsetTopologyManagerService(ITopologyManager s) {
        log.trace("Unset TopologyManagerService.");

        if (  topologyManager == s) {
            topologyManager = null;
        }
    }

    @Override
    public PacketResult receiveDataPacket(RawPacket inPkt) {
      //Once a packet come the Topology has to be updated
      if(counter == MAXPACKETCOUNTER){

        updateTopology();
        counter = 0;
      }else{
        counter++;
      }

      //First I get the incoming Connector where the packet came.
      NodeConnector ingressConnector = inPkt.getIncomingNodeConnector();
      Packet pkt = dataPacketService.decodeDataPacket(inPkt);
      log.trace("The packet came from " + ingressConnector + " NodeConnector");

      //Now we obtain the node where we received the packet
      Node node = ingressConnector.getNode();
      log.trace("The packet came from " + node + " Node");

      if(!hasHostConnected(ingressConnector)){
        Edge upEdge = getUpEdge(node, ingressConnector);
        if(upEdge != null){
          calculateLatency(upEdge, pkt);
        }
      }

      if(pkt instanceof Ethernet) {
        //Pass the Ethernet Packet
        Ethernet ethFrame = (Ethernet) pkt;
        byte[] srcMAC_B = (ethFrame).getSourceMACAddress();
        long srcMAC = BitBufferHelper.toNumber(srcMAC_B);
        byte[] dstMAC_B = (ethFrame).getDestinationMACAddress();
        long dstMAC = BitBufferHelper.toNumber(dstMAC_B);
        Object l3Pkt = ethFrame.getPayload();

        if(l3Pkt instanceof IPv4){
          IPv4 ipv4Pkt = (IPv4)l3Pkt;
          InetAddress srcAddr = intToInetAddress(ipv4Pkt.getSourceAddress());
          InetAddress dstAddr = intToInetAddress(ipv4Pkt.getDestinationAddress());
          Object l4Datagram = ipv4Pkt.getPayload();

          if(l4Datagram instanceof ICMP){

            return handleICMPPacket(inPkt, srcAddr, srcMAC_B, ingressConnector, node, dstAddr, dstMAC_B);

          }else if(l4Datagram instanceof UDP){

            UDP udpDatagram = (UDP) l4Datagram;
            int clientPort = udpDatagram.getSourcePort();
            int dstPort = udpDatagram.getDestinationPort();


            byte[] udpRawPayload = udpDatagram.getRawPayload();

            if(detectRTPPacket(udpRawPayload, dstPort)){
              return handleRTPPacket(inPkt, srcAddr, srcMAC_B, ingressConnector, node, dstAddr, dstMAC_B, dstPort);
            }

          }else if(l4Datagram instanceof TCP){
            TCP tcpDatagram = (TCP) l4Datagram;
            int clientPort = tcpDatagram.getSourcePort();
            int dstPort = tcpDatagram.getDestinationPort();

            byte[] tcpRawPayload = tcpDatagram.getRawPayload();
          }

        }
      }
      return PacketResult.IGNORED;
    }

    /**
     * Function called by the dependency manager when all the required
     * dependencies are satisfied
     *
     */
    @SuppressWarnings({ "unchecked", "rawtypes" })
    public void init() {
        log.debug("Routing init() is called");
        this.nodeEdges=new HashMap<Node, Set<Edge>>();
        updateTopology();

    }

    /**
     * Function called by the dependency manager when at least one dependency
     * become unsatisfied or when the component is shutting down because for
     * example bundle is being stopped.
     *
     */
    void destroy() {
        log.debug("Routing destroy() is called");
    }

    /**
    *Function which build the edgeMatrix
    *@param edges the topologyMap
    */

    private void buildEdgeMatrix(Map<Node, Set<Edge>> edges){

      this.edgeMatrix = null;
      this.edgeMatrix = new Edge[edges.size()][edges.size()];
      Set<Node> nodes = edges.keySet();

      for(Iterator<Node> it = nodes.iterator(); it.hasNext();){

        Node nodeTemp = it.next();
        Set<Edge> nodeEdges = edges.get(nodeTemp);

        for(Iterator<Edge> it2 = nodeEdges.iterator(); it2.hasNext();){

          Edge edgeTemp = it2.next();
          putEdge(edgeTemp);

        }

      }
    }

    /**
    *This function try to assing a cost for each Edge attending the latency and
    *medium latency and other aspects like statistics
    */

    private void buildStandardCostMatrix(){
      int l = this.nodeEdges.size();
      int h = this.nodeEdges.size();
      this.standardCostMatrix = new Long[l][h];
      this.edgeCostMap.clear();

      for(int i=0; i<l; i++){

        for(int j=0; j<h; j++){

          if(i==j){
            this.standardCostMatrix[i][j]=0L;
          }
          else{
            if(this.edgeMatrix[i][j]==null){
              this.standardCostMatrix[i][j]=null;
            }
            else{
              this.standardCostMatrix[i][j] = standardLatencyCost(this.edgeMatrix[i][j]) +
              standardStatisticsMapCost(this.edgeMatrix[i][j])/10;
            }
          }
          edgeCostMap.put(this.edgeMatrix[i][j], this.standardCostMatrix[i][j]);
        }
      }
      buildTransformerMap(this.edgeCostMap);
    }

    /**
    *This function try to assing a cost for each Edge attending The video factors
    *which is different to Standard evaluation
    */

    private void buildRTPCostMatrix(){
      int l = this.nodeEdges.size();
      int h = this.nodeEdges.size();
      this.rtpCostMatrix = new Long[l][h];
      this.rtpEdgeCostMap.clear();

      for(int i=0; i<l; i++){

        for(int j=0; j<h; j++){

          if(i==j){
            this.rtpCostMatrix[i][j]=0L;
          }
          else if(this.edgeMatrix[i][j]==null){
            this.rtpCostMatrix[i][j]=null;
          }
          else{

            this.rtpCostMatrix[i][j] = rtpLatencyCost(this.edgeMatrix[i][j])/RTPFACTOR +
            rtpStatisticsCost(this.edgeMatrix[i][j])/10;
          }

          this.rtpEdgeCostMap.put(this.edgeMatrix[i][j], this.rtpCostMatrix[i][j]);
        }
      }
      buildRTPTransformerMap(this.rtpEdgeCostMap);
    }

    /**
    *Function that is called when is necessary to build the transformer for Dijkstra
    */

    private void buildTransformerMap(final Map<Edge, Long> edgeCostMap2){

      costTransformer = new Transformer<Edge, Long>(){
        public Long transform(Edge e){

          return edgeCostMap2.get(e);
        }
      };

    }

    /**
    *Function that is called when is necessary to build the transformer rtp for Dijkstra
    */

    private void buildRTPTransformerMap(final Map<Edge, Long> rtpEdgeCostMap2){

      this.costRTPTransformer = new Transformer<Edge, Long>(){
        public Long transform(Edge e){

          return rtpEdgeCostMap2.get(e);
        }
      };

    }

    /**
    *This function is called when a Packet come and is necessary to calculate the latency
    *@param edge The associate edge
    *@param packet The packet which came just now
    */

    private void calculateLatency(Edge edge, Packet packet){

      Set<Packet> temp = this.edgePackets.get(edge);
      if(checkSetPacket(packet, temp)){
        temp.remove(packet);
        this.edgePackets.remove(edge);
        this.edgePackets.put(edge, temp);
        Long t2 = System.nanoTime();
        Long t1 = returnPacketTime(edge, packet);

        if(t1!=null){
          Long t = t2-t1;
          updateLatencyMatrix(edge, t);
          if(minLatency == null){
            minLatency=t;
          }
          else if(minLatency> t){
            minLatency=t;
          }
        }

      }

    }

    /**
    *Function that is called when is necessary check if a IPAddress are in memory or not
    *@param node The node where we have to check
    *@param addr The IPAddress which is necessary to check
    *@return The boolean which shows if the Address are or not.
    */

    private boolean checkAddress(Node node, InetAddress addr){

      Map<Node, InetAddress> temp = new HashMap<Node, InetAddress>();
      temp.put(node, addr);
      return this.tableIP.containsKey(temp);

    }

    /**
    *This function is called when is necessary to check if the latencyMatrix is complete or not
    *@return result The boolean which indics if the matrix are complete or not
    */

    private boolean checkLatencyMatrix(){

      boolean result = true;
      if(this.edgeMatrix==null || this.latencyMatrix==null){
        return false;
      }

      for(int i=0; i<this.edgeMatrix.length; i++){
        for(int j=0; j<this.edgeMatrix[i].length; j++){

          if(edgeMatrix[i][j] != null){
            if(latencyMatrix[i][j] == null){

              return false;
            }

          }

        }
      }
      return true;

    }

    /**
    *This function check is a Packet is contained in a Set<Packet>
    *@param packet The packet
    *@param packets The set of packets
    *@return true if is contained or farse is not
    */

    private boolean checkSetPacket(Packet packet, Set<Packet> packets){

      for(Iterator<Packet> it = packets.iterator(); it.hasNext();){

        Packet temp = it.next();
        if(temp.equals(packet)){
          return true;
        }
      }

      return false;

    }

    /**Function that is called when is necessary to compare the statistics
    *@param m1 The HeadNodeConnector Statistic
    *@param m2 The tailNodeConnector Statistic
    *@param compare The string which identify the statistic
    */

    private void compareStatistic(Long m1, Long m2, String compare){

      Long temp = this.maxStatistics.get(compare);

      if(m1>m2){
        if(temp==null){
          temp=m1;
          this.maxStatistics.put(compare, temp);
        }else if(m1>temp){
            temp=m1;
            this.maxStatistics.remove(compare);
            this.maxStatistics.put(compare, temp);
          }
      }else{
        if(temp==null){
          temp=m2;
          this.maxStatistics.put(compare, temp);
        }else if(m2>temp){
            temp=m2;
            this.maxStatistics.remove(compare);
            this.maxStatistics.put(compare, temp);
          }
      }

    }

    /**
    *This function is called when is required to build a topology Graph
    */

    private void createTopologyGraph(){
      g = new SparseMultigraph();

      for(int i=0; i<edgeMatrix.length; i++){
        for(int j=0; j<edgeMatrix[i].length; j++){

          if(edgeMatrix[i][j]!=null){
            g.addEdge(edgeMatrix[i][j], edgeMatrix[i][j].getTailNodeConnector().getNode(),
            edgeMatrix[i][j].getHeadNodeConnector().getNode());
          }

        }
      }
    }

    /**
    *Function that is called when a edge is down
    *@param edge The edge which is down.
    *@param node The node where the edge is detected
    */

    private boolean delFlow(Edge edge, Node node){

      NodeConnector tempConnector = edge.getTailNodeConnector();
      Node tempNode = tempConnector.getNode();
      boolean result = false;
      List<FlowOnNode> flowsOnNode = new ArrayList();

        if(tempNode.equals(node)){
          log.debug("hola");

          try{
            flowsOnNode = statisticsManager.getFlowsNoCache(tempNode);
          }
          catch(RuntimeException bad){
            log.debug("impossible to obtain the flows on the node "+tempNode);
          }
          log.debug("adios");

          for(int i=0; i<flowsOnNode.size(); i++){


              FlowOnNode tempFlowOnNode = flowsOnNode.get(i);
              Flow tempFlow = tempFlowOnNode.getFlow();

              if(tempFlow!=null){
                List<Action> oldActions = tempFlow.getActions();

                if(oldActions!=null){
                  List<Action> tempActions = new ArrayList<Action>();
                  tempActions.add(new Output(tempConnector));

                  if(tempActions.equals(oldActions)){
                    log.debug("Deleting flow with outputAction "+tempConnector+ " in the node "+node);

                    flowProgrammerService.removeFlow(tempNode, tempFlow);

                  }
                }
              }

          }
      }
      return result;
    }


    //-128, -95 are the number value of the two first packets rtp which combined with the destination port are enough to detect rtp packet and program flow

    /*
    Número de versión de RTP (V - versión number): 2 bits. La versión definida por la especificación actual es 2.
    Relleno (P - Padding): 1 bit. Si el bit del relleno está activado, hay uno o más bytes al final del paquete que no es parte de la carga útil. El último byte del paquete indica el número de bytes de relleno. El relleno es usado por algunos algoritmos de cifrado.
    La extensión (X - Extensión): 1 bit. Si el bit de extensión está activado, entonces el encabezado fijo es seguido por una extensión del encabezado. Este mecanismo de la extensión posibilita implementaciones para añadir información al encabezado RTP.
    Conteo CSRC (CC): 4 bits. El número de identificadores CSRC que sigue el encabezado fijo. Si la cuenta CSRC es cero, entonces la fuente de sincronización es la fuente de la carga útil.
    El marcador (M - Marker): 1 bit. Un bit de marcador definido por el perfil particular de media.
    Tipo de Carga útil (PT - Payload Type): 7 bits. Un índice en una tabla del perfiles de media que describe el formato de carga útil. Los mapeos de carga útil para audio y vídeo están especificados en el RFC 1890.
    */

    /**
    *Function that is called when is necessary to check if a Packet is RTP
    *@param rawPayload The payload of the packet
    *@param dstPort The dstPort for the packet
    *@return True or false.
    */

    private boolean detectRTPPacket(byte[] rawPayload, int dstPort){
      boolean result = false;

      if(dstPort == rtpPort){
        Byte temp = rawPayload[0];
        String tempString = Integer.toBinaryString((temp & 0xFF) + 0x100).substring(1);

        if(tempString.equals(RTPSTRING)){
          result=true;
        }

      }
      return result;
    }

    /**
    *This function return the NodeConnector where a Host is attached
    *@param srcIP The inetAddress
    *@return NodeConnector The NodeConnector where the InetAddress is attached
    */

    private NodeConnector findHost(InetAddress srcIP){

      Set<NodeConnector> connectors = this.topologyManager.getNodeConnectorWithHost();

      for (Iterator<NodeConnector> it = connectors.iterator(); it.hasNext(); ) {
         NodeConnector temp = it.next();
         List<Host> hosts= this.topologyManager.getHostsAttachedToNodeConnector(temp);

         for(Iterator<Host> ith = hosts.iterator(); ith.hasNext();){

           Host temp2 = ith.next();
           if(temp2.getNetworkAddress().equals(srcIP)){
             return temp;
           }

         }

      }
      return null;

    }

    /**
    *Function that is called when is necessary flood a determinate packet for all the nodeConnector in a node
    *@param inPkt pakect that we have to flood
    *@param node the node which solicite the listenDataPacketService
    *@param ingressConnector the "port" where the Packet came
    */

    private void floodPacket(RawPacket inPkt, Node node, NodeConnector ingressConnector) {

        Set<NodeConnector> nodeConnectors =
        this.switchManager.getUpNodeConnectors(node);
        Packet pkt = dataPacketService.decodeDataPacket(inPkt);

        for (NodeConnector p : nodeConnectors) {
          if (!p.equals(ingressConnector)) {
            try {

              RawPacket destPkt = new RawPacket(inPkt);

              if(!hasHostConnected(p)){
                Edge downEdge = getDownEdge(node, p);
                if(downEdge!=null){
                  putPacket(downEdge, pkt);
                }
              }
              destPkt.setOutgoingNodeConnector(p);
              this.dataPacketService.transmitDataPacket(destPkt);

            }
            catch (ConstructionException e2) {
              continue;
            }
          }
        }
    }

    /**
    *Function that is called when is necessary to obtain a Edge through a NodeConnector
    *We suppose that each NodeConnector has only one Edge and the nodeConnector is the head
    *@param node The actual node
    *@param node The required node
    *@param InetAddres The IP required
    *@return NodeConnector The Connector for this association.
    */

    private NodeConnector getIPNodeConnector(Node node, InetAddress addr){

      Map<Node, InetAddress> temp = new HashMap<Node, InetAddress>();
      temp.put(node, addr);
      return this.tableIP.get(temp);

    }

    /**
    *Function that is called when is necessary to obtain a Edge through a NodeConnector
    *We suppose that each NodeConnector has only one Edge and the NodeConnector is the Head
    *@param node The actual node
    *@param connector The NodeConnector which identify the Edge
    *@return The Edge corresponding the nodeConnector
    */

    private Edge getDownEdge(Node node, NodeConnector connector){
      Set<Edge> edges = this.nodeEdges.get(node);

      for(Iterator<Edge> it = edges.iterator(); it.hasNext();){
        Edge temp = it.next();

        if(temp.getHeadNodeConnector().equals(connector)){
          log.trace("Found the DOWN edge corresponding the connector " + connector + " " + temp);
          return temp;
        }

      }
      return null;
    }

    /**
    *This method provide the possibility to get a index for a nodeConnector
    *@param nodeConnector The nodeConnector.
    */

    private int getNodeConnectorIndex(NodeConnector nodeConnector){

      int index;
      Node node = nodeConnector.getNode();
      index = Integer.parseInt(node.getID().toString());
      return index-1;

    }

    /**
    *Function that is called when is necessary to obtain a Edge through a NodeConnector
    *We suppose that each NodeConnector has only one Edge and the NodeConnector is the Tail
    *@param node The actual node
    *@param connector The NodeConnector which identify the Edge
    *@return The Edge corresponding the nodeConnector
    */

    private Edge getUpEdge(Node node, NodeConnector connector){
      Set<Edge> edges = this.nodeEdges.get(node);

      for(Iterator<Edge> it = edges.iterator(); it.hasNext();){
        Edge temp = it.next();

        if(temp.getTailNodeConnector().equals(connector)){
          log.trace("Found the UP edge corresponding the connector " + connector + " " + temp);
          return temp;
        }

      }
      return null;
    }

    /**
    *This function return true if the NodeConnector has some Host attached
    *@param connector The NodeConnector
    *@return true if yes or false if not
    */

    private boolean hasHostConnected(NodeConnector connector){

      if(topologyManager.getHostsAttachedToNodeConnector(connector) != null){
        return true;
      }
      else{
        return false;
      }

    }

    /**
    *Function that is called when a ICMP Packet needs to be Handled
    *@param inPKt The received Packet
    *@param srcAddr The src IP Address
    *@param srcMAC_B The src MAC Address in bytes
    *@param ingressConnector The connector where the packet came
    *@param node The node where the packet have been received
    *@param dstAddr The dst IP Address
    *@param dstMAC_B The dst MAC Address in bytes
    *@return result The result of handle the ICMP Packet
    */

    private PacketResult handleICMPPacket(RawPacket inPkt, InetAddress srcAddr, byte[] srcMAC_B,
    NodeConnector ingressConnector, Node node, InetAddress dstAddr, byte[] dstMAC_B){

      Packet pkt = dataPacketService.decodeDataPacket(inPkt);
      NodeConnector egressConnector=null;
      PacketResult result = null;

      if(flood<MAXFLOODPACKET){
        this.flood++;
        floodPacket(inPkt, node, ingressConnector);
      }else{

        NodeConnector tempSrcConnector = findHost(srcAddr);
        Node tempSrcNode = tempSrcConnector.getNode();
        NodeConnector tempDstConnector = findHost(dstAddr);
        Node tempDstNode = tempDstConnector.getNode();

        Map<Node, Node> tempMap = new HashMap<Node, Node>();
        tempMap.put(tempSrcNode, tempDstNode);

        List<Edge> tempPath = new ArrayList<Edge>();


        if(icmpPathMap.containsKey(tempMap)){
         tempPath = icmpPathMap.get(tempMap);
        }else{
         this.standardShortestPath = new DijkstraShortestPath<Node,Edge>(this.g, this.costTransformer);
         tempPath = standardShortestPath.getPath(tempSrcNode, tempDstNode);
         icmpPathMap.put(tempMap, tempPath);
        }

        List<Edge> definitivePath;

        boolean temp = tempPath.get(0).getTailNodeConnector().getNode().equals(tempSrcNode);

        if(!temp){
          definitivePath = reordenateList(tempPath, tempSrcNode, tempDstNode);
        }
        else{
          definitivePath = tempPath;
        }
        if(definitivePath != null){

          egressConnector = installListFlows(definitivePath, srcAddr, srcMAC_B, dstAddr, dstMAC_B, node,
          tempSrcConnector, tempDstConnector);


          if(!hasHostConnected(egressConnector)){
            Edge downEdge = getDownEdge(node, egressConnector);
            if(downEdge!= null){
              putPacket(downEdge, pkt);
            }
          }

          if(egressConnector!= null){
          //Send the packet for the selected Port.
            inPkt.setOutgoingNodeConnector(egressConnector);
            this.dataPacketService.transmitDataPacket(inPkt);
          }else{
            floodPacket(inPkt, node, ingressConnector);
          }
          /********************************************Debug**********************************
          */

          /*
          log.debug("" + this.latencyMatrix[0][1]);
          log.debug("" + this.mediumLatencyMatrix[0][1]);
          log.debug("" + this.standardCostMatrix[0][1]);


          /*************************************** ***Debug***************************************/
          result = PacketResult.CONSUME;

        }else{
          log.trace("Destination host is unrecheable!");
          result = PacketResult.IGNORED;
        }
      }

      return result;

    }

    /**
    *Function that is called when a RTP Packet needs to be Handled
    *@param inPKt The received Packet
    *@param srcAddr The src IP Address
    *@param srcMAC_B The src MAC Address in bytes
    *@param ingressConnector The connector where the packet came
    *@param node The node where the packet have been received
    *@param dstAddr The dst IP Address
    *@param dstMAC_B The dst MAC Address in bytes
    *@param dstPort The RTP dstPort that identify the protocol
    *@return result The result of handle the RTP Packet
    */

    private PacketResult handleRTPPacket(RawPacket inPkt, InetAddress srcAddr, byte[] srcMAC_B,
    NodeConnector ingressConnector, Node node, InetAddress dstAddr, byte[] dstMAC_B, int dstPort){

      Packet pkt = dataPacketService.decodeDataPacket(inPkt);
      NodeConnector egressConnector=null;
      PacketResult result = null;

      if(flood<MAXFLOODPACKET){
        this.flood++;
        floodPacket(inPkt, node, ingressConnector);
      }else{

        NodeConnector tempSrcConnector = findHost(srcAddr);
        Node tempSrcNode = tempSrcConnector.getNode();
        NodeConnector tempDstConnector = findHost(dstAddr);
        Node tempDstNode = tempDstConnector.getNode();

        Map<Node, Node> tempMap = new HashMap<Node, Node>();
			  tempMap.put(tempSrcNode, tempDstNode);

			  List<Edge> tempPath = new ArrayList<Edge>();


        if(rtpPathMap.containsKey(tempMap)){
				 tempPath = rtpPathMap.get(tempMap);
			  }else{
				 this.rtpShortestPath = new DijkstraShortestPath<Node,Edge>(this.g, this.costRTPTransformer);
				 tempPath = rtpShortestPath.getPath(tempSrcNode, tempDstNode);
				 rtpPathMap.put(tempMap, tempPath);
			  }

        List<Edge> definitivePath;

        boolean temp = tempPath.get(0).getTailNodeConnector().getNode().equals(tempSrcNode);

        if(!temp){
          definitivePath = reordenateList(tempPath, tempSrcNode, tempDstNode);
        }
        else{
          definitivePath = tempPath;
        }
        if(definitivePath != null){

          egressConnector = installRTPListFlows(definitivePath, srcAddr, srcMAC_B, dstAddr, dstMAC_B, node,
          tempSrcConnector, tempDstConnector, dstPort);


          if(!hasHostConnected(egressConnector)){
            Edge downEdge = getDownEdge(node, egressConnector);
            if(downEdge!= null){
              putPacket(downEdge, pkt);
            }
          }

          if(egressConnector!= null){
          //Send the packet for the selected Port.
            inPkt.setOutgoingNodeConnector(egressConnector);
            this.dataPacketService.transmitDataPacket(inPkt);
          }else{
            floodPacket(inPkt, node, ingressConnector);
          }
          result = PacketResult.CONSUME;

        }else{
          log.trace("Destination host is unrecheable!");
          result = PacketResult.IGNORED;
        }
      }

      return result;
    }

    /**
    *This function initialize the map edgeMediumTime
    */

    private void initializeEdgeMediumTime(){

      Set<Edge> edges = this.topologyManager.getEdges().keySet();

      ArrayList<Long> temp;

      for(Iterator<Edge> it = edges.iterator(); it.hasNext();){
        temp= new ArrayList();
        Edge tempEdge = it.next();

        edgeMediumMapTime.put(tempEdge, temp);
      }

    }

    /**
    *Function that is called when is necesarry to install a List of flows
    *All the flows will have two timeOut, idle and Hard.
    *@param path The Edge List
    *@param srcAddr The source IPv4 Address
    *@param srcMAC_B The srcMACAddress in byte format
    *@param dstAddr The destination IPV4 Address
    *@param dstMAC_B The dstMACAddress in byte format
    *@param node The node where we have to return the egressConnector
    *@param srcConnector The Connector src
    *@param dstConnector The Connector dst
    *@return The NodeConnector for the node
    */

    private NodeConnector installListFlows(List<Edge> path, InetAddress srcAddr, byte[] srcMAC_B,
    InetAddress dstAddr, byte[] dstMAC_B, Node node, NodeConnector srcConnector, NodeConnector dstConnector){
      NodeConnector result = null;
      for(int i=0; i<path.size();i++){
        Edge tempEdge = path.get(i);
        NodeConnector tempConnector = tempEdge.getTailNodeConnector();
        Node tempNode = tempConnector.getNode();
        if(tempNode.equals(node)){
          result = tempConnector;
        }

        if(programFlow( srcAddr, srcMAC_B, dstAddr, dstMAC_B, tempConnector, tempNode) ){

          log.trace("Flow installed on " + node + " in the port " + tempConnector);

        }
        else{
          log.trace("Error trying to install the flow");
        }

      }

      if(programFlow( srcAddr, srcMAC_B, dstAddr, dstMAC_B, dstConnector, dstConnector.getNode()) ){

        log.trace("Flow installed on " + dstConnector.getNode() + " in the port " + dstConnector);

      }
      else{
        log.trace("Error trying to install the flow");
      }


      return result;
    }

    /**
    *Function that is called when is necesarry to install a List of flows
    *All the flows will have two timeOut, idle and Hard.
    *@param path The Edge List
    *@param srcAddr The source IPv4 Address
    *@param srcMAC_B The srcMACAddress in byte format
    *@param dstAddr The destination IPV4 Address
    *@param dstMAC_B The dstMACAddress in byte format
    *@param node The node where we have to return the egressConnector
    *@param srcConnector The Connector src
    *@param dstConnector The Connector dst
    *@param dstPort The rtp destination Port
    *@return The NodeConnector for the node
    */

    private NodeConnector installRTPListFlows(List<Edge> path, InetAddress srcAddr, byte[] srcMAC_B,
    InetAddress dstAddr, byte[] dstMAC_B, Node node, NodeConnector srcConnector, NodeConnector dstConnector, int dstPort){
      NodeConnector result = null;
      for(int i=0; i<path.size();i++){
        Edge tempEdge = path.get(i);
        NodeConnector tempConnector = tempEdge.getTailNodeConnector();
        Node tempNode = tempConnector.getNode();
        if(tempNode.equals(node)){
          result = tempConnector;
        }

        if(programRTPFlow( srcAddr, srcMAC_B, dstAddr, dstMAC_B, tempConnector, tempNode, dstPort) ){

          log.trace("Flow installed on " + node + " in the port " + tempConnector);

        }
        else{
          log.trace("Error trying to install the flow");
        }

        if(i == path.size()-1){
          NodeConnector lastConnector = findHost(dstAddr);
          Node lastNode = lastConnector.getNode();


            if(programRTPFlow( srcAddr, srcMAC_B, dstAddr, dstMAC_B, lastConnector, lastNode, dstPort) ){

              log.trace("Flow installed on " + lastNode + " in the port " + lastConnector);

            }
            else{
              log.trace("Error trying to install the flow");
            }

        }

      }

      ///////////////////////The dst node will have a flow for the IP

      return result;
    }

    /**
    *Function that is called when is necessary to put a Association Node,IP and NodeConnector
    *in ourt IPTable.
    *@param node The node where we have to create the association.
    *@param InetAddres The IP Address
    *@param NodeConnector The NodeConnector where the Packet came.
    */

    private void learnIPAddress(Node node, InetAddress addr, NodeConnector connector){

      Map<Node, InetAddress> temp = new HashMap<Node, InetAddress>();
      temp.put(node, addr);
      this.tableIP.remove(temp);
      this.tableIP.put(temp, connector);

    }

    /**
    *Function that is called when is necesarry to install a flow
    *All the flows will have two timeOut, idle and Hard.
    *@param srcAddr The source IPv4 Address
    *@param srcMAC_B The srcMACAddress in byte format
    *@param dstAddr The destination IPV4 Address
    *@param dstMAC_B The dstMACAddress in byte format
    *@param outConnector The dstConnector that will install on the node
    *@param node The node where the flow will be installed
    */

    synchronized private boolean programFlow(InetAddress srcAddr, byte[] srcMAC_B, InetAddress dstAddr,
    byte[] dstMAC_B, NodeConnector outConnector, Node node) {

        Match match = new Match();
        match.setField(MatchType.DL_TYPE, (short) 0x0800);  // IPv4 ethertype
        match.setField(MatchType.NW_PROTO, IPProtocols.ICMP.byteValue());
        match.setField(MatchType.NW_SRC, srcAddr);
        match.setField(MatchType.NW_DST, dstAddr);
        match.setField(MatchType.DL_SRC, srcMAC_B);
        match.setField(MatchType.DL_DST, dstMAC_B);

        List<Action> actions = new ArrayList<Action>();
        actions.add(new Output(outConnector));

        Flow f = new Flow(match, actions);

        // Create the flow
        Flow flow = new Flow(match, actions);

        flow.setIdleTimeout(idleTimeOut);
        flow.setHardTimeout(hardTimeOut);

        // Use FlowProgrammerService to program flow.
        Status status = flowProgrammerService.addFlowAsync(node, flow);

        if (!status.isSuccess()) {
            log.debug("Could not program flow: " + status.getDescription());
            return false;
        }
        else{
        return true;
      }

    }

    /**
    *Function that is called when is necesarry to install a flow
    *All the flows will have two timeOut, idle and Hard.
    *@param srcAddr The source IPv4 Address
    *@param srcMAC_B The srcMACAddress in byte format
    *@param dstAddr The destination IPV4 Address
    *@param dstMAC_B The dstMACAddress in byte format
    *@param outConnector The dstConnector that will install on the node
    *@param node The node where the flow will be installed
    *@param dstPort The destination Port for RTP Packet
    */

    synchronized private boolean programRTPFlow(InetAddress srcAddr, byte[] srcMAC_B, InetAddress dstAddr,
    byte[] dstMAC_B, NodeConnector outConnector, Node node, int dstPort) {

        Match match = new Match();
        match.setField(MatchType.DL_TYPE, (short) 0x0800);  // IPv4 ethertype
        match.setField(MatchType.NW_SRC, srcAddr);
        match.setField(MatchType.NW_DST, dstAddr);
        match.setField(MatchType.DL_SRC, srcMAC_B);
        match.setField(MatchType.DL_DST, dstMAC_B);
        match.setField(MatchType.TP_DST, (short) dstPort);
        match.setField(MatchType.NW_PROTO, IPProtocols.UDP.byteValue());

        List<Action> actions = new ArrayList<Action>();
        actions.add(new Output(outConnector));

        Flow f = new Flow(match, actions);

        // Create the flow
        Flow flow = new Flow(match, actions);

        flow.setIdleTimeout(idleTimeOut);
        //flow.setHardTimeout(hardTimeOut);

        // Use FlowProgrammerService to program flow.
        Status status = flowProgrammerService.addFlowAsync(node, flow);
        if (!status.isSuccess()) {
            log.error("Could not program flow: " + status.getDescription());
            return false;
        }
        else{
        return true;
      }

    }

    /**
    *Function that is called when is necessary to put a edge in the edgeMatrix
    *@param edge The edge that it will be put in the matrix.
    */

    private void putEdge(Edge edge){

      int node1 = getNodeConnectorIndex(edge.getTailNodeConnector());
      int node2 = getNodeConnectorIndex(edge.getHeadNodeConnector());

      this.edgeMatrix[node1][node2] = edge;
      log.trace("Put the edge in the position: " + node1 + " " +node2);

    }

    /**
    *Function that is called when is necessary to add a Edge to statistics
    *@param edge The edge
    */

    private void putEdgeStatistics(Edge edge){

      NodeConnector head = edge.getHeadNodeConnector();
      NodeConnector tail = edge.getTailNodeConnector();

      NodeConnectorStatistics headStatistics = this.statisticsManager.getNodeConnectorStatistics(head);
      NodeConnectorStatistics tailStatistics = this.statisticsManager.getNodeConnectorStatistics(tail);

      Long m1, m2;

      //////////////////////////////////
      ArrayList<Long> tempArray = new ArrayList<Long>();
      m1=headStatistics.getTransmitByteCount();
      m2=tailStatistics.getTransmitByteCount();
      tempArray.add(m1);
      tempArray.add(m2);
      compareStatistic(m1, m2, transmitBytes);

      Map<String, ArrayList> tempMap =  new HashMap<String, ArrayList>();
      tempMap.put(transmitBytes, tempArray);

      /////////////////////////////
      tempArray=new ArrayList<Long>();
      m1=headStatistics.getReceiveByteCount();
      m2=tailStatistics.getReceiveByteCount();
      tempArray.add(m1);
      tempArray.add(m2);

      compareStatistic(m1, m2, receiveBytes);

      tempMap.put(receiveBytes, tempArray);
      //////////////////////////////////
      tempArray=new ArrayList<Long>();
      m1=headStatistics.getTransmitDropCount();
      m2=tailStatistics.getTransmitDropCount();
      tempArray.add(m1);
      tempArray.add(m2);

      compareStatistic(m1, m2, transmitDropBytes);

      tempMap.put(transmitDropBytes, tempArray);
      /////////////////////////////////////
      tempArray=new ArrayList<Long>();
      m1=headStatistics.getReceiveDropCount();
      m2=tailStatistics.getReceiveDropCount();
      tempArray.add(m1);
      tempArray.add(m2);

      compareStatistic(m1, m2, receiveDropBytes);

      tempMap.put(receiveDropBytes, tempArray);
      ///////////////////////////////////////
      tempArray=new ArrayList<Long>();
      m1=headStatistics.getTransmitErrorCount();
      m2=tailStatistics.getTransmitErrorCount();
      tempArray.add(m1);
      tempArray.add(m2);

      compareStatistic(m1, m2, transmitErrorBytes);

      tempMap.put(transmitErrorBytes, tempArray);
      ///////////////////////////////////////
      tempArray=new ArrayList<Long>();
      m1=headStatistics.getReceiveErrorCount();
      m2=tailStatistics.getReceiveErrorCount();
      tempArray.add(m1);
      tempArray.add(m2);

      compareStatistic(m1, m2, receiveErrorBytes);

      tempMap.put(receiveErrorBytes, tempArray);
      ///////////////////////////////////////
      this.edgeStatistics.put(edge, tempMap);

    }

    /**
    *This function put a new association Edge Packet en the Map and put the thime in the PacketTime map
    *@parameter edge The edge
    *@parameter packet The packet
    */

    private void putPacket(Edge edge, Packet packet){

      Set<Packet> temp = this.edgePackets.get(edge);

      if(temp != null){
        if(temp.contains(packet)){
          temp.remove(packet);
          this.edgePackets.remove(edge);
          this.edgePackets.put(edge, temp);
          removePacketTime(edge, packet);
        }
        else{
          temp.add(packet);
          this.edgePackets.remove(edge);
          this.edgePackets.put(edge, temp);
          Long t = System.nanoTime();
          Map<Edge, Packet> temp2 = new HashMap<Edge, Packet>();
          temp2.put(edge, packet);
          this.packetTime.put(temp2, t);
        }
      }
      else{
        temp = new HashSet<Packet>();
        temp.add(packet);
        this.edgePackets.remove(edge);
        this.edgePackets.put(edge, temp);
        Long t = System.nanoTime();

        Map<Edge, Packet> temp2 = new HashMap<Edge, Packet>();

        temp2.put(edge, packet);
        this.packetTime.put(temp2, t);
      }

    }

    /**
    *Function that is called when is necessary to check the flows on the nodes
    *@param edges The new node association Set<Edge> that have to be compared with the old topology
    */

    synchronized private void removeOldFlow(Map<Node, Set<Edge>> edges){
      Set<Node> nodes = edges.keySet();

      for(Iterator<Node> it = nodes.iterator(); it.hasNext();){

        Node tempNode = it.next();
        Set<Edge> tempEdgesOld = this.nodeEdges.get(tempNode);
        Set<Edge> tempEdgesNew = edges.get(tempNode);

        if(tempEdgesOld!=null && tempEdgesNew!=null){

          if(tempEdgesNew.size() < tempEdgesOld.size()){

            for(Iterator<Edge> it2 = tempEdgesOld.iterator(); it2.hasNext();){
              boolean success = false;
              Edge tempEdge = it2.next();

              if(!tempEdgesNew.contains(tempEdge)){
                log.debug("The edge "+tempEdge+ " in the node "+tempNode+" is down");

                delFlow(tempEdge, tempNode);


            }

          }
        }
          /*
          else if(tempEdgesNew.size() > tempEdgesOld.size()){
            for(Iterator<Edge> it2 = tempEdgesOld.iterator(); it2.hasNext();){

              Edge tempEdge = it2.next();

              if(!tempEdgesOld.contains(tempEdge)){
                log.debug("The edge "+tempEdge+ " in the node "+tempNode+" is a new Edge");
                delFlow(tempEdge, tempNode);

              }
            }
          }
          */
        }
      }
    }

    /**
    *This function is called when a association Edge, Packet, Time are wrong.
    *@param edge The edge identificator
    *@param packet The packet
    */

    private void removePacketTime(Edge edge, Packet packet){

      Map<Edge, Packet> temp = new HashMap<Edge, Packet>();
      temp.put(edge, packet);
      this.packetTime.remove(temp);

    }

    /**
    *This function reordenate a Edge<List> to put in the correct order.
    *@param path The List<Edge>
    *@param srcNode The first Node
    *@param dstNode The last Node
    *@return The definitive List<Edge>
    */

    private List<Edge> reordenateList(List<Edge> path, Node srcNode, Node dstNode){
      boolean orden = true;
      boolean orientacion = true;

      List<Edge> result = new ArrayList();
      List<Edge> definitivePath = new ArrayList();

      if(path.get(0).getTailNodeConnector().getNode().equals(srcNode)){
        orden=true;
        orientacion=true;
      }
      else if(path.get(0).getHeadNodeConnector().getNode().equals(srcNode)){
        orden=true;
        orientacion=false;
      }
      else if(path.get(path.size()-1).getTailNodeConnector().getNode().equals(srcNode)){
        orden=false;
        orientacion=true;
      }
      else if(path.get(path.size()-1).getHeadNodeConnector().getNode().equals(srcNode)){
        orden=false;
        orientacion=false;
      }

      int i=0;
      int n1=0;
      int n2=0;

      if(!orden){
        i=path.size()-1;
      }
      int index;
      for(int j=0; j<path.size();j++){

        if(!orden){
          index=i-j;
        }
        else{
          index=j;
        }

        Edge tempEdge = path.get(index);

        if(!orientacion){
          n1=getNodeConnectorIndex(tempEdge.getHeadNodeConnector());
          n2=getNodeConnectorIndex(tempEdge.getTailNodeConnector());
        }else{
          n1=getNodeConnectorIndex(tempEdge.getTailNodeConnector());
          n2=getNodeConnectorIndex(tempEdge.getHeadNodeConnector());
        }
        result.add(this.edgeMatrix[n1][n2]);
      }

      ////////////////////////
      //Better reordenating
      ///////////////////////

      definitivePath.add(result.get(0));


      for(int j=1; j<result.size(); j++){

        Edge tempEdge2 = result.get(j);
        Edge tempEdge1 = result.get(j-1);

        Node tempNode1 = tempEdge1.getHeadNodeConnector().getNode();
        Node tempNode2 = tempEdge2.getTailNodeConnector().getNode();

        Node tempNodeAux = tempEdge2.getHeadNodeConnector().getNode();


        if(tempNode1.equals(tempNode2)){
          definitivePath.add(result.get(j));
        }else if(tempNode1.equals(tempNodeAux)){
          int aux1 = getNodeConnectorIndex(tempEdge2.getHeadNodeConnector());
          int aux2 = getNodeConnectorIndex(tempEdge2.getTailNodeConnector());

          definitivePath.add(this.edgeMatrix[aux1][aux2]);
        }
      }

      return definitivePath;

    }

    /**
    *This function restart the latency and mediumLatencyMatrix
    */

    private void resetLatencyMatrix(){
      this.latencyMatrix = new Long[this.nodeEdges.size()][this.nodeEdges.size()];
      this.mediumLatencyMatrix = new Long[this.nodeEdges.size()][this.nodeEdges.size()];
      initializeEdgeMediumTime();
    }

    /**
    *This function return the time for a Edge Packet association
    *@param edge The edge
    *@param packet The packet
    *@return time The stored time
    */

    private Long returnPacketTime(Edge edge, Packet packet){

      Set<Map<Edge,Packet>> temp = this.packetTime.keySet();
      Map<Edge, Packet> temp2 = new HashMap<Edge, Packet>();
      temp2.clear();
      temp2.put(edge, packet);

      for(Iterator<Map<Edge, Packet>> it = temp.iterator(); it.hasNext();){

        Map<Edge, Packet> temp3 = it.next();
        if(temp3.equals(temp2)){
          Long time = this.packetTime.get(temp3);
          this.packetTime.remove(temp3);
          log.trace("Returning time for the solicitated packet" +time);
          return time;
        }
      }

      return null;

    }

    /**
    *This function is called when is necessary evaluate the latencyMatrix for an edge and
    *rtp protocol
    *@param edge The edge
    *@return The Long value after the process
    */

    private Long rtpLatencyCost(Edge edge){
      int i = getNodeConnectorIndex(edge.getTailNodeConnector());
      int j = getNodeConnectorIndex(edge.getHeadNodeConnector());

      Long ret1 = 0L;
      Long ret2 = 0L;

      Long cost = 0L;
      if(latencyMatrix!=null){
        Long temp1 = this.latencyMatrix[i][j];
        Long temp2 = this.mediumLatencyMatrix[i][j];

        if(temp1 == null){
          ret1=RTPDEFAULTCOST;
        }
        if(temp2 == null){
          ret2=RTPDEFAULTCOST;
        }

        if(temp1 != null && temp2 != null){
          if(temp1>temp2){
            cost = (temp1 - temp2)/2;
          }
          else if (temp2>temp1){
            cost = (temp2 - temp1)/2;
          }else{
            cost = RTPDEFAULTCOST*2;
          }
        }
      }
      else{
        ret1=RTPDEFAULTCOST;
        ret2=RTPDEFAULTCOST;
        cost=ret1+ret2;
      }
      return cost;
    }

    /**
    *This function is called when is necessary evaluate the statisticsMap for an edge and
    *rtp protocol
    *@param edge The edge
    *@return The Long value after the process
    */

    private Long rtpStatisticsCost(Edge edge){
      Long cost = 0L;
      Long temp1 = 0L;
      Long temp2 = 0L;

      ArrayList<Long> tempArray = new ArrayList<Long>();

      Map<String, ArrayList> tempStatistics = this.edgeStatistics.get(edge);
      for(int i=0; i<statisticsName.length; i++){
        tempArray = tempStatistics.get(statisticsName[i]);

        if(tempArray == null){

          tempArray=new ArrayList<Long>();
          tempArray.add(10L);
          tempArray.add(10L);

        }

        if(tempArray.get(0)!=0 && tempArray.get(1) !=0 ){
          Long tempMedium = (tempArray.get(0) + tempArray.get(1) )/ 2;

          Long tempMax = maxStatistics.get(statisticsName[i]);

          if(tempMax == null){
            tempMax = tempMedium;
          }


          if(tempMax/tempMedium > 9){
            cost += 1L;
          }
          else{
            cost += 10L - tempMax/tempMedium;
          }
        }
        else{
          cost += 1L;
        }
      }
      return cost/5;
    }

    /**
    *This function is called when is necessary evaluate the latencyMatrix for an edge
    *@param edge The edge
    *@return The Long value after the process
    */

    private Long standardLatencyCost(Edge edge){
      int i = getNodeConnectorIndex(edge.getTailNodeConnector());
      int j = getNodeConnectorIndex(edge.getHeadNodeConnector());

      Long ret1 = 0L;
      Long ret2 = 0L;

      Long cost;
      if(latencyMatrix!=null){
        Long temp = this.latencyMatrix[i][j];
        Long temp2 = this.mediumLatencyMatrix[i][j];

        if(temp == null){
          ret1=defaultCost;
        }
        else{
          ret1 = temp/minLatency;
        }

        if(temp2 == null){
          ret2=defaultCost;
        }
        else{
          ret2=temp2/minMediumLatency;
        }
      }
      else{
        ret1=defaultCost;
        ret2=defaultCost;
      }

      cost = ret1/2 + ret2;
      return cost;
    }

    /**
    *This function is called when is necessary evaluate the statisticsMap for an edge
    *@param edge The edge
    *@return The Long value after the process
    */

    private Long standardStatisticsMapCost(Edge edge){
      Long cost = 0L;
      Long temp1 = 0L;
      Long temp2 = 0L;

      ArrayList<Long> tempArray = new ArrayList<Long>();

      Map<String, ArrayList> tempStatistics = this.edgeStatistics.get(edge);
      for(int i=0; i<statisticsName.length; i++){
        tempArray = tempStatistics.get(statisticsName[i]);

        if(tempArray == null){

          tempArray=new ArrayList<Long>();
          tempArray.add(10L);
          tempArray.add(10L);

        }

        if(tempArray.get(0)!=0 && tempArray.get(1) !=0 ){
          Long tempMedium = (tempArray.get(0) + tempArray.get(1) )/ 2;

          Long tempMax = maxStatistics.get(statisticsName[i]);

          if(tempMax == null){
            tempMax = tempMedium;
          }


          if(tempMax/tempMedium > 9){
            cost += 1L;
          }
          else{
            cost += 10L - tempMax/tempMedium;
          }
        }
        else{
          cost += 1L;
        }
      }
      return cost/2;
    }

    /**
    *This function is called when is necessary to sum all the elements of a Array
    *@param array The array which will be sum
    *@return result The complete sum of the array
    */

    private Long sumLongArray(ArrayList<Long> array){
      Long result = 0L;

      for(int i=0; i<array.size(); i++){

        result += array.get(i);

      }

      return result;
    }

    /**
    *Function that is called when we pretend to show in log all the elements of a Matrix
    *@matrix[][] The matrix
    */

    private void traceEdgeMatrix(Edge matrix[][]){

      for(int i=0; i<matrix.length; i++){
        for(int j=0; j<matrix[i].length; j++){

          log.debug("Element "+i+ " "+j+" is: "+matrix[i][j]);

        }
      }

    }

    /**
    *Function that is called when we pretend to show in log all the elements of a Matrix
    *@matrix[][] The matrix
    */

    private void traceLongMatrix(Long matrix[][]){

      for(int i=0; i<matrix.length; i++){
        for(int j=0; j<matrix[i].length; j++){

          log.debug("Element "+i+ " "+j+" is: "+matrix[i][j]);

        }
      }

    }

    /**
    *The follow function update the latencyMatrix for the position of the edge
    *@param edge The edge
    *@param t The latency time.
    */

    private void updateLatencyMatrix(Edge edge, Long t){

      int node1 = getNodeConnectorIndex(edge.getTailNodeConnector());
      int node2 = getNodeConnectorIndex(edge.getHeadNodeConnector());

      ArrayList<Long> temp = this.edgeMediumMapTime.get(edge);

      if(temp.size()==5){
        temp.remove(0);
        temp.add(t);
      }
      else{
        temp.add(t);
      }

      this.edgeMediumMapTime.remove(edge);
      this.edgeMediumMapTime.put(edge, temp);

      Long sum = sumLongArray(temp);

      this.mediumLatencyMatrix[node1][node2] = sum / temp.size();

      if(minMediumLatency == null){
        this.minMediumLatency = sum / temp.size();
      }
      else{
        if(this.minMediumLatency > (sum/ temp.size())){
          this.minMediumLatency = sum / temp.size();
        }
      }

      this.latencyMatrix[node1][node2] = t;
      log.trace("Put the Latency: " + t + " in the position: " + node1 + " " +node2);
    }

    /**
    *Function that is called when is necessary update the statistics.
    */

    private void updateEdgeStatistics(){
      this.edgeStatistics.clear();
      Set<Node> tempNodes = this.nodeEdges.keySet();
      for(Iterator<Node> it = tempNodes.iterator(); it.hasNext();){
        Node tempNode = it.next();
        Set<Edge> tempEdges = this.nodeEdges.get(tempNode);
          for(Iterator<Edge> it2 = tempEdges.iterator(); it2.hasNext();){
            Edge tempEdge = it2.next();
            putEdgeStatistics(tempEdge);
          }
      }

    }

    /**
    *Function that is called when is necessary update the current Topology store
    */

    synchronized private void updateTopology(){

      Map<Node, Set<Edge>> edges = this.topologyManager.getNodeEdges();

      if(nodeEdges.isEmpty() || !nodeEdges.equals(edges)){

        MAXFLOODPACKET = 3*this.nodeEdges.size();

        this.packetTime.clear();
        this.edgePackets.clear();
        this.rtpPathMap.clear();
        this.icmpPathMap.clear();
        flood=0;

        if(this.nodeEdges!=null && edges!=null){

          removeOldFlow(edges);
        }

        this.nodeEdges = edges;
        buildEdgeMatrix(edges);
        log.trace("The new map is " + this.nodeEdges);
        resetLatencyMatrix();
        createTopologyGraph();

        log.debug("The topology has been updated");
      }

      updateEdgeStatistics();
      buildStandardCostMatrix();
      buildRTPCostMatrix();
    }

}
