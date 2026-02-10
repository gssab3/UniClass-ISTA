<%@ page contentType="text/html; charset=UTF-8" pageEncoding="UTF-8" %>
<%@ page import="it.unisa.uniclass.utenti.model.Utente" %>
<%@ page import="it.unisa.uniclass.utenti.model.Accademico" %>
<%@ page import="it.unisa.uniclass.utenti.model.Ruolo" %>
<%@ page import="it.unisa.uniclass.utenti.model.Tipo" %>

<%
    /* Recupero Sessione */
    HttpSession sessione = request.getSession(false);
    if(sessione == null || sessione.getAttribute("currentSessionUser") == null) {
        response.sendRedirect("Login.jsp");
        return;
    }

    Utente user = (Utente) sessione.getAttribute("currentSessionUser");
    session.setAttribute("utenteEmail", user.getEmail());

    /* Variabili per visualizzazione unificata */
    String uNome = user.getNome();
    String uCognome = user.getCognome();
    String uDataNascita = "Data di nascita: " + user.getDataNascita();
    String uEmail = user.getEmail();
    String uDataIscrizione = "Iscritto dal: " + user.getIscrizione();

    // Default per generico Utente (ex Personale TA)
    String uMatricolaOrId = "ID: Non disponibile";
    String uCorsoOrTelefono = "Tel: " + (user.getTelefono() != null ? user.getTelefono() : "N/D");
    String userIcon = "images/icons/usericonnolog.png";

    // Determina il tipo per il menu laterale
    boolean isAccademico = false;
    boolean isPersonaleTA = true; // Di default se non è accademico

    /* Logica specifica per Accademico (Polimorfismo) */
    if (user instanceof Accademico) {
        Accademico acc = (Accademico) user;
        isAccademico = true;
        isPersonaleTA = false;

        uMatricolaOrId = acc.getMatricola();

        if (acc.getCorsoLaurea() != null) {
            uCorsoOrTelefono = acc.getCorsoLaurea().getNome();
        } else {
            uCorsoOrTelefono = "Nessun corso assegnato";
        }

        // Gestione Icone in base al Ruolo
        if (acc.getRuolo() == Ruolo.STUDENTE) {
            userIcon = "images/icons/iconstudent.png";
        } else if (acc.getRuolo() == Ruolo.DOCENTE || acc.getRuolo() == Ruolo.COORDINATORE) {
            userIcon = "images/icons/iconprof.png";
        }
    } else {
        // Logica per Utente Generico (Personale TA)
        userIcon = "images/icons/iconpersonaleTA.png";
        // Qui si potrebbe usare user.getTipo() se l'enum Tipo esiste ancora per distinguere admin
    }
%>

<!DOCTYPE html>
<html lang="it" xml:lang="it">

<head>
    <title>UniClass Account</title>
    <script src="scripts/sidebar.js" type="text/javascript"></script>
    <link type="text/css" rel="stylesheet" href="styles/headerStyle.css" />
    <link type="text/css" rel="stylesheet" href="styles/barraNavigazioneStyle.css"/>
    <link type="text/css" rel="stylesheet" href="styles/informazioniStyle.css">
    <link rel="icon" href="images/logois.png" sizes="32x32" type="image/png">
</head>

<body>

<div class="barraNavigazione" id="barraNavigazione">
    <a href="javascript:void(0)" class="closebtn" onclick="closeNav()">
        <img src="images/icons/menuOpenIcon.png" alt="closebtn">
    </a>
    <p>Menu</p>
    <ul id="menu">
        <li id="aule"><a href="aula.jsp">Aule</a></li>

        <%-- Menu condizionale --%>
        <% if(isPersonaleTA) { %>
        <li id="gutenti"><a href="PersonaleTA/AttivaUtenti.jsp">Gestione Utenti</a></li>
        <% } else { %>
        <li id="conversazioni"><a href="Conversazioni">Conversazioni</a></li>
        <% } %>

        <li id="mappa"><a href="mappa.jsp">Mappa</a></li>
        <li id="ChatBot"><a href="ChatBot.jsp">ChatBot</a></li>
        <li id="infoapp"><a href="infoapp.jsp">Info App</a></li>
        <li id="aboutus"><a href="aboutus.jsp">Chi Siamo</a></li>
    </ul>
</div>

<jsp:include page="header.jsp" />

<div class="listaInfo" id="listaInfo">
    <h2>Informazioni</h2>
    <ul id="infolist">
        <img src="<%= userIcon %>" alt="immagineutente">

        <li id="nome"><%= uNome %></li>
        <li id="cognome"><%= uCognome %></li>
        <li id="dataNascita"><%= uDataNascita %></li>

        <%-- ID / Matricola --%>
        <% if (isAccademico) { %>
        <li id="matricola"><%= uMatricolaOrId %></li>
        <% } else { %>
        <li id="id"><%= uMatricolaOrId %></li>
        <% } %>

        <li id="email"><%= uEmail %></li>

        <%-- Corso / Telefono --%>
        <% if (isAccademico) { %>
        <li id="corsoLaurea"><%= uCorsoOrTelefono %></li>
        <li id="dataIscrizione"><%= uDataIscrizione %></li>
        <% } else { %>
        <li id="telefono"><%= uCorsoOrTelefono %></li>
        <% } %>
    </ul>

    <form action="LogoutServlet" method="post">
        <button type="submit" class="logout-button">Logout</button>
    </form>
</div>

</body>
</html>