<%@ page contentType="text/html; charset=UTF-8" pageEncoding="UTF-8" %>
<%@ page import="it.unisa.uniclass.utenti.model.Utente, it.unisa.uniclass.utenti.model.Tipo" %>
<%@ page import="it.unisa.uniclass.orari.model.CorsoLaurea" %>
<%@ page import="java.util.List" %>
<%@ page import="it.unisa.uniclass.orari.service.AulaService" %>

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



    List<String> edificitotali = (List<String>) request.getAttribute("edificitotali");
    // Nota: corsiLaurea recuperato ma non utilizzato nel display corrente, mantenuto per compatibilità
    List<CorsoLaurea> corsiLaurea = (List<CorsoLaurea>) request.getAttribute("corsi");
%>

<!DOCTYPE html>
<html lang="it" xml:lang="it">
<head>
    <title>Aule</title>
    <script src="scripts/sidebar.js" type="text/javascript"></script>
    <link type="text/css" rel="stylesheet" href="styles/headerStyle.css"/>
    <link type="text/css" rel="stylesheet" href="styles/barraNavigazioneStyle.css"/>
    <link type="text/css" rel="stylesheet" href="styles/formcss.css"/>
    <link type="text/css" rel="stylesheet" href="styles/footerstyle.css">
    <link type="text/css" rel="stylesheet" href="styles/aulastyle.css">
    <link rel="icon" href="images/logois.png" sizes="32x32" type="image/png">
</head>
<body>

<div class="barraNavigazione" id="barraNavigazione">
    <a href="javascript:void(0)" class="closebtn" onclick="closeNav()">
        <img src="images/icons/menuOpenIcon.png" alt="closebtn">
    </a>
    <p>Menu</p>
    <ul id="menu">
        <li id="aule"><a href="AulaServlet">Aule</a></li>

        <%-- Voci menu per utenti loggati --%>
        <% if (tipoUtente != null) { %>

        <%-- Solo Studente vede Agenda
        <% if (tipoUtente.equals(Tipo.Studente)) { %>
        <li id="agenda"><a href="servelt">Agenda</a></li>
        <% } %>  --%>

        <%-- Tutti gli utenti loggati vedono Appelli (in base al codice originale)
        <li id="appelli"><a href="servelt">Appelli</a></li>--%>

        <%-- Gestione differenziata: PersonaleTA vs Altri --%>
        <% if (tipoUtente.equals(Tipo.PersonaleTA)) { %>
        <li id="gutenti"><a href="PersonaleTA/AttivaUtenti.jsp">Gestione Utenti</a></li>
        <% } else {
            // Studente, Docente, Coordinatore vedono Conversazioni
        %>
        <li id="conversazioni"><a href="Conversazioni">Conversazioni</a></li>
        <% } %>

        <% } %>

        <li id="mappa"><a href="mappa.jsp">Mappa</a></li>
        <li id="ChatBot"><a href="ChatBot.jsp">ChatBot</a></li>
        <li id="infoapp"><a href="infoapp.jsp">Info App</a></li>
        <li id="aboutus"><a href="aboutus.jsp">Chi Siamo</a></li>
    </ul>
</div>

<jsp:include page="header.jsp"/>

<br>
<br>

<h1>Edifici</h1>
<br>

<div class="container-wrapper">
    <%
        if (edificitotali != null) {
            for(String edificio: edificitotali) {
    %>
    <div class="container">
        <h2><a href="EdificioServlet?ed=<%=edificio%>">Edificio <%=edificio%></a></h2>
    </div>
    <%      }
    }
    %>
</div>

<br>
<br>
<br>
<%@include file = "footer.jsp" %>
</body>
</html>