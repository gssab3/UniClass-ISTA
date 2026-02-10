<%@ page contentType="text/html; charset=UTF-8" pageEncoding="UTF-8" %>
<%@ page import="it.unisa.uniclass.utenti.model.Utente, it.unisa.uniclass.utenti.model.Tipo" %>
<%@ page import="it.unisa.uniclass.orari.model.CorsoLaurea" %>
<%@ page import="java.util.List" %>
<%@ page import="it.unisa.uniclass.orari.service.dao.CorsoLaureaDAO" %>
<%@ page import="it.unisa.uniclass.utenti.model.Accademico" %>
<%@ page import="it.unisa.uniclass.utenti.service.AccademicoService" %>
<%@ page import="it.unisa.uniclass.conversazioni.model.Messaggio" %>
<%@ page import="java.util.ArrayList" %>
<%@ page import="it.unisa.uniclass.utenti.model.Ruolo" %>

<%
  /* Sessione HTTP */
  HttpSession sessione = request.getSession(true);
  Utente user = (Utente) sessione.getAttribute("currentSessionUser");
  if(user != null){
    session.setAttribute("utenteEmail", user.getEmail());
  }

  /* Controllo tipo utente */
  Tipo tipoUtente = null;

  if (user != null) {
    tipoUtente = user.getTipo();

    if (tipoUtente == Tipo.PersonaleTA) {
      response.sendRedirect("ErroreAccesso.jsp");
      return;
    }
  }
  else {
    response.sendRedirect("Login.jsp");
    return;
  }

  Accademico accademicoSelf = (Accademico) request.getAttribute("accademicoSelf");
  List<Messaggio> messaggi = new ArrayList<Messaggio>();

  if (accademicoSelf == null) {
    response.sendRedirect("Login.jsp");
    return;
  }

  if (accademicoSelf != null) {
    List<Messaggio> msgAttr = (List<Messaggio>) request.getAttribute("messaggi");
    if (msgAttr != null) {
      messaggi = msgAttr;
    }
  }
%>

<!DOCTYPE html>
<html lang="it" xml:lang="it">

<head>
  <title>UniClass Chat</title>
  <script src="scripts/sidebar.js" type="text/javascript"></script>
  <link type="text/css" rel="stylesheet" href="styles/headerStyle.css"/>
  <link type="text/css" rel="stylesheet" href="styles/barraNavigazioneStyle.css"/>
  <link type="text/css" rel="stylesheet" href="styles/conversazioniStyle.css">
  <link type="text/css" rel="stylesheet" href="styles/newChat.css">
  <link type="text/css" rel="stylesheet" href="styles/footerstyle.css">
  <link rel="icon" href="images/logois.png" sizes="32x32" type="image/png">
</head>

<body id="uniClassChat">

<div class="barraNavigazione" id="barraNavigazione">
  <a href="javascript:void(0)" class="closebtn" onclick="closeNav()">
    <img src="images/icons/menuOpenIcon.png" alt="closebtn">
  </a>
  <p>Menu</p>
  <ul id="menu">
    <li id="aule"><a href="AulaServlet">Aule</a></li>
    <li id="conversazioni"><a href="Conversazioni">Conversazioni</a></li>
    <li id="mappa"><a href="mappa.jsp">Mappa</a></li>
    <li id="ChatBot"><a href="ChatBot.jsp">ChatBot</a></li>
    <li id="infoapp"><a href="infoapp.jsp">Info App</a></li>
    <li id="aboutus"><a href="aboutus.jsp">Chi Siamo</a></li>
  </ul>
</div>

<jsp:include page="header.jsp"/>

<div class="mega-container">
  <h1>Conversazioni</h1>
  <div class="conversations-container">
    <%
      List<Accademico> accademiciFor = new ArrayList<>();
      if (accademicoSelf != null) {
        for(Messaggio m: messaggi) {
          // Logica per filtrare gli utenti con cui c'è una conversazione
          Accademico other = null;
          boolean isAutoreSelf = m.getAutore().getEmail().equals(accademicoSelf.getEmail());
          boolean isDestSelf = m.getDestinatario().getEmail().equals(accademicoSelf.getEmail());

          if (isDestSelf && !accademiciFor.contains(m.getAutore())) {
            other = m.getAutore();
          } else if (isAutoreSelf && !accademiciFor.contains(m.getDestinatario())) {
            other = m.getDestinatario();
          }

          if (other != null) {
            accademiciFor.add(other);
          }
        }
      }

      for(Accademico accademico : accademiciFor) {
        String iconPath = "images/icons/usericonnolog.png"; // Default
        if(accademico.getRuolo().equals(Ruolo.STUDENTE)){
          iconPath = "images/icons/iconstudent.png";
        } else if (accademico.getRuolo().equals(Ruolo.DOCENTE) || accademico.getRuolo().equals(Ruolo.COORDINATORE)) {
          iconPath = "images/icons/iconprof.png";
        }
    %>
    <a href="chatServlet?accademico=<%=accademico.getEmail()%>&accademicoSelf=<%=accademicoSelf.getEmail()%>" class="conversation">
      <div class="profile-picture">
        <img src="<%= iconPath %>" alt="Foto profilo">
      </div>
      <div class="username"><%=accademico.getNome()%> <%=accademico.getCognome()%></div>
    </a>
    <% } %>
  </div>
</div>


<h1>Crea una nuova Chat</h1>

<div class="form-container">
  <form id="myForm" action="invioMessaggioServlet" method="post" class="chat-form">
    <label for="email" class="form-label">Seleziona un'email:</label>
    <select id="email" name="email" class="form-select">
      <% if(accademicoSelf.getRuolo().equals(Ruolo.DOCENTE) || accademicoSelf.getRuolo().equals(Ruolo.COORDINATORE)) { %>
      <option value="tutti">Annuncio</option>
      <% } %>
    </select>

    <br><br>

    <% if(accademicoSelf.getRuolo().equals(Ruolo.DOCENTE) || accademicoSelf.getRuolo().equals(Ruolo.COORDINATORE)) { %>
    <label for="topic" class="form-label">Topic:</label>
    <textarea id="topic" name="topic" class="form-textarea" rows="5" cols="40"></textarea>
    <br><br>
    <% } else { %>
    <input type="hidden" name="topic" value="null"/>
    <% } %>

    <label for="testo" class="form-label">Testo del messaggio:</label>
    <textarea id="testo" name="testo" class="form-textarea" rows="5" cols="40"></textarea>

    <br><br>

    <button type="submit" class="form-button">Invia</button>
  </form>
</div>

<script src="scripts/formChat.js" defer></script>
<%@include file = "footer.jsp" %>
</body>
</html>