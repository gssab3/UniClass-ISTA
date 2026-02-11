<%@ page import="it.unisa.uniclass.utenti.model.Utente" %>
<%@ page import="it.unisa.uniclass.utenti.model.Tipo" %>
<%@ page import="java.util.List" %>
<%@ page import="it.unisa.uniclass.orari.model.*" %>
<%@ page import="java.time.LocalTime" %>
<%@ page import="java.util.stream.Collectors" %>
<%@ page contentType="text/html;charset=UTF-8" language="java" %>

<%
  /* Sessione HTTP */
  HttpSession sessione = request.getSession(true);
  Utente user = (Utente) sessione.getAttribute("currentSessionUser");
  if(user != null){
    session.setAttribute("utenteEmail", user.getEmail());
  }

  /* Controllo tipo utente */
  Tipo tipoUtente = null;
  if(user != null) {
    tipoUtente = (Tipo) user.getTipo();
  }

  CorsoLaurea corsoLaurea = (CorsoLaurea) request.getAttribute("corsoLaurea");
  Resto resto = (Resto) request.getAttribute("resto");
  AnnoDidattico annoDidattico = (AnnoDidattico) request.getAttribute("anno");
  List<Lezione> lezioni = (List<Lezione>) request.getAttribute("lezioni");
%>

<!DOCTYPE html>
<html lang="it" xml:lang="it">
<head>
  <title>Orario UniClass</title>
  <script src="scripts/sidebar.js" type="text/javascript"></script>
  <link type="text/css" rel="stylesheet" href="styles/headerStyle.css"/>
  <link type="text/css" rel="stylesheet" href="styles/barraNavigazioneStyle.css"/>
  <link type="text/css" rel="stylesheet" href="styles/formcss.css"/>
  <link type="text/css" rel="stylesheet" href="styles/tableStyle.css">
  <link type="text/css" rel="stylesheet" href="styles/footerstyle.css">
  <link rel="icon" href="images/logois.png" sizes="32x32" type="image/png">
  <style>
    .schedule-table td { height: 50px; }
    .schedule-table th { background-color: #f2f2f2; }
    .subject-base { background-color: #e3f2fd; border-left: 5px solid #2196f3; padding: 5px; font-size: 0.9em; }
  </style>
</head>
<body>

<div class="barraNavigazione" id="barraNavigazione">
  <a href="javascript:void(0)" class="closebtn" onclick="closeNav()">
    <img src="images/icons/menuOpenIcon.png" alt="closebtn">
  </a>
  <p>Menu</p>
  <ul id="menu">
    <li id="aule"><a href="AulaServlet">Aule</a></li>

    <% if (tipoUtente != null) { %>
    <% if (tipoUtente.equals(Tipo.PersonaleTA)) { %>
    <li id="gutenti"><a href="PersonaleTA/AttivaUtenti.jsp">Gestione Utenti</a></li>
    <% } else { %>
    <li id="conversazioni"><a href="Conversazioni">Conversazioni</a></li>
    <% } %>
    <% } %>

    <li id="home"><a href="Home">Home</a></li>
    <li id="aboutus"><a href="aboutus.jsp">Chi Siamo</a></li>
  </ul>
</div>

<jsp:include page="header.jsp"/>

<br>
<h1 style="text-align: center;">
  ORARIO: <%= corsoLaurea != null ? corsoLaurea.getNome() : "N/D" %>
  - <%= resto != null ? resto.getNome() : "N/D" %>
  - <%= annoDidattico != null ? annoDidattico.getAnno() : "N/D" %>
</h1>
<br>

<div class="table-container">
  <%
    // APERTURA IF PRINCIPALE
    if (lezioni == null || lezioni.isEmpty()) {
  %>
  <h3 style="text-align: center; color: red;">Nessuna lezione trovata per i parametri selezionati.</h3>
  <%
  } else { // APERTURA ELSE PRINCIPALE
  %>
  <table class="schedule-table" border="1" style="width: 95%; margin: 0 auto; border-collapse: collapse;">
    <tr>
      <th>Giorno</th>
      <th>9:00</th><th>9:30</th><th>10:00</th><th>10:30</th>
      <th>11:00</th><th>11:30</th><th>12:00</th><th>12:30</th>
      <th>13:00</th><th>13:30</th><th>14:00</th><th>14:30</th>
      <th>15:00</th><th>15:30</th><th>16:00</th><th>16:30</th>
      <th>17:00</th><th>17:30</th>
    </tr>
    <%
      // Ciclo per ogni giorno della settimana
      for (Giorno giorno : Giorno.values()) {
        if (giorno.toString().equals("DOMENICA")) continue;
    %>
    <tr>
      <td class="highlight" style="font-weight: bold; background-color: #eee;"><%= giorno.toString() %></td>
      <%
        int currentSlot = 18; // 9:00 * 2 = 18
        int maxSlot = 36;     // 18:00 * 2 = 36

        // Filtra le lezioni di questo giorno
        List<Lezione> lezioniDelGiorno = lezioni.stream()
                .filter(l -> l.getGiorno() == giorno)
                .collect(Collectors.toList());

        for (Lezione lezione : lezioniDelGiorno) {
          LocalTime start = lezione.getOraInizio().toLocalTime();
          LocalTime end = lezione.getOraFine().toLocalTime();

          int startSlot = start.getHour() * 2 + (start.getMinute() >= 30 ? 1 : 0);
          int endSlot = end.getHour() * 2 + (end.getMinute() >= 30 ? 1 : 0);
          int duration = endSlot - startSlot;

          // Riempi spazi vuoti prima della lezione
          while (currentSlot < startSlot && currentSlot < maxSlot) {
      %>
      <td></td>
      <%
          currentSlot++;
        }

        // Stampa la cella della lezione
        if (currentSlot == startSlot) {
          String nomeCorso = (lezione.getCorso() != null) ? lezione.getCorso().getNome() : "Corso ?";
          String aulaNome = (lezione.getAula() != null) ? lezione.getAula().getNome() : "?";
          String docenti = "Prof. N/D";

          if (lezione.getAccademici() != null && !lezione.getAccademici().isEmpty()) {
            docenti = lezione.getAccademici().stream()
                    .map(d -> d.getCognome())
                    .collect(Collectors.joining(", "));
          }
      %>
      <td colspan="<%= duration %>" class="subject-base" style="text-align: center; vertical-align: middle;">
        <strong><%= nomeCorso %></strong><br>
        <small><%= docenti %></small><br>
        <small>Aula: <%= aulaNome %></small>
      </td>
      <%
            currentSlot += duration;
          }
        }

        // Riempi le celle rimanenti fino alle 18:00
        while (currentSlot < maxSlot) {
      %>
      <td></td>
      <%
          currentSlot++;
        }
      %>
    </tr>
    <%
      } // CHIUSURA FOR (Giorno)
    %>
  </table>
  <%
    } // CHIUSURA ELSE PRINCIPALE
  %>
</div>

<br><br><br>
<%@include file = "footer.jsp" %>
</body>
</html>