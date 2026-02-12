package it.unisa.uniclass.testing.unit.conversazioni.controller;

import it.unisa.uniclass.conversazioni.controller.inviaMessaggioChatServlet;
import it.unisa.uniclass.conversazioni.model.Messaggio;
import it.unisa.uniclass.conversazioni.model.Topic;
import it.unisa.uniclass.conversazioni.service.MessaggioService;
import it.unisa.uniclass.utenti.model.Accademico;
import it.unisa.uniclass.orari.model.CorsoLaurea;
import jakarta.servlet.ServletException;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.mockito.ArgumentCaptor;
import org.mockito.Mock;
import org.mockito.MockitoAnnotations;

import java.io.IOException;
import java.time.LocalDateTime;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.ArgumentMatchers.anyString;
import static org.mockito.Mockito.*;

/**
 * Test completi per inviaMessaggioChatServlet.
 * Copertura massimizzata per JaCoCo.
 */
public class inviaMessaggioChatServeltTest {

    @Mock
    private MessaggioService messaggioService;

    @Mock
    private AccademicoService accademicoService;

    @Mock
    private HttpServletRequest request;

    @Mock
    private HttpServletResponse response;

    @Mock
    private HttpSession session;

    private inviaMessaggioChatServlet servlet;

    private Accademico accademicoMittente;
    private Accademico accademicoDestinatario;
    private CorsoLaurea corsoLaurea;
    private Messaggio messaggioSalvato;

    @BeforeEach
    public void setUp() {
        MockitoAnnotations.openMocks(this);

        servlet = new inviaMessaggioChatServlet();
        servlet.setMessaggioService(messaggioService);
        servlet.setAccademicoService(accademicoService);
        when(request.getServletContext()).thenReturn(mock(jakarta.servlet.ServletContext.class));

        // Setup CorsoLaurea
        corsoLaurea = new CorsoLaurea();
        corsoLaurea.setNome("Informatica");

        // Setup Accademico Mittente
        accademicoMittente = new Accademico();
        accademicoMittente.setEmail("mittente@unisa.it");
        accademicoMittente.setNome("Mario");
        accademicoMittente.setCognome("Rossi");
        accademicoMittente.setMatricola("0512100001");
        accademicoMittente.setCorsoLaurea(corsoLaurea);

        // Setup Accademico Destinatario
        accademicoDestinatario = new Accademico();
        accademicoDestinatario.setEmail("destinatario@unisa.it");
        accademicoDestinatario.setNome("Luigi");
        accademicoDestinatario.setCognome("Verdi");
        accademicoDestinatario.setMatricola("0512100002");
        accademicoDestinatario.setCorsoLaurea(corsoLaurea);

        // Setup Topic
        Topic topic = new Topic();
        topic.setNome("VUOTO");
        topic.setCorsoLaurea(corsoLaurea);

        // Setup Messaggio salvato
        messaggioSalvato = new Messaggio();
        messaggioSalvato.setAutore(accademicoMittente);
        messaggioSalvato.setDestinatario(accademicoDestinatario);
        messaggioSalvato.setBody("Ciao, come stai?");
        messaggioSalvato.setDateTime(LocalDateTime.now());
        messaggioSalvato.setTopic(topic);
    }

    @Test
    public void testDoGetSuccessfulMessageSending() throws ServletException, IOException {
        System.out.println("\n=== Test 1: Invio messaggio standard ===");

        // Arrange
        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utenteEmail")).thenReturn("mittente@unisa.it");
        when(request.getParameter("emailInvio")).thenReturn("destinatario@unisa.it");
        when(request.getParameter("testo")).thenReturn("Ciao, come stai?");

        when(accademicoService.trovaEmailUniClass("mittente@unisa.it")).thenReturn(accademicoMittente);
        when(accademicoService.trovaEmailUniClass("destinatario@unisa.it")).thenReturn(accademicoDestinatario);
        when(messaggioService.aggiungiMessaggio(any(Messaggio.class))).thenReturn(messaggioSalvato);

        List<Messaggio> messaggi = new ArrayList<>();
        messaggi.add(messaggioSalvato);
        when(messaggioService.trovaTutti()).thenReturn(messaggi);

        List<Accademico> messaggeri = new ArrayList<>();
        messaggeri.add(accademicoDestinatario);
        when(messaggioService.trovaMessaggeriDiUnAccademico(anyString())).thenReturn(messaggeri);

        // Act
        servlet.doGet(request, response);

        // Assert
        verify(accademicoService).trovaEmailUniClass("mittente@unisa.it");
        verify(accademicoService).trovaEmailUniClass("destinatario@unisa.it");

        ArgumentCaptor<Messaggio> messaggioCaptor = ArgumentCaptor.forClass(Messaggio.class);
        verify(messaggioService).aggiungiMessaggio(messaggioCaptor.capture());

        Messaggio messaggioInviato = messaggioCaptor.getValue();
        assertNotNull(messaggioInviato);
        assertEquals("Ciao, come stai?", messaggioInviato.getBody());
        assertEquals(accademicoMittente, messaggioInviato.getAutore());
        assertEquals(accademicoDestinatario, messaggioInviato.getDestinatario());
        assertEquals("VUOTO", messaggioInviato.getTopic().getNome());
        assertEquals(corsoLaurea, messaggioInviato.getTopic().getCorsoLaurea());
        assertNotNull(messaggioInviato.getDateTime());

        verify(messaggioService).trovaTutti();
        verify(messaggioService).trovaMessaggeriDiUnAccademico("0512100001");
        verify(request).setAttribute("messaggi", messaggi);
        verify(request).setAttribute("accademici", messaggeri);
        verify(response).sendRedirect("chatServlet?accademico=destinatario@unisa.it&accademicoSelf=mittente@unisa.it");

        System.out.println("✓ Test completato con successo");
    }

    @Test
    public void testDoGetWithLongMessage() throws ServletException, IOException {
        System.out.println("\n=== Test 2: Invio messaggio lungo ===");

        String longMessage = "Lorem ipsum dolor sit amet, consectetur adipiscing elit. ".repeat(10);

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utenteEmail")).thenReturn("mittente@unisa.it");
        when(request.getParameter("emailInvio")).thenReturn("destinatario@unisa.it");
        when(request.getParameter("testo")).thenReturn(longMessage);

        when(accademicoService.trovaEmailUniClass("mittente@unisa.it")).thenReturn(accademicoMittente);
        when(accademicoService.trovaEmailUniClass("destinatario@unisa.it")).thenReturn(accademicoDestinatario);

        Messaggio messaggioLungo = new Messaggio();
        messaggioLungo.setBody(longMessage);
        messaggioLungo.setAutore(accademicoMittente);
        messaggioLungo.setDestinatario(accademicoDestinatario);
        messaggioLungo.setDateTime(LocalDateTime.now());
        Topic topic = new Topic();
        topic.setNome("VUOTO");
        topic.setCorsoLaurea(corsoLaurea);
        messaggioLungo.setTopic(topic);

        when(messaggioService.aggiungiMessaggio(any(Messaggio.class))).thenReturn(messaggioLungo);
        when(messaggioService.trovaTutti()).thenReturn(new ArrayList<>());
        when(messaggioService.trovaMessaggeriDiUnAccademico(anyString())).thenReturn(new ArrayList<>());

        servlet.doGet(request, response);

        ArgumentCaptor<Messaggio> captor = ArgumentCaptor.forClass(Messaggio.class);
        verify(messaggioService).aggiungiMessaggio(captor.capture());
        assertEquals(longMessage, captor.getValue().getBody());

        System.out.println("✓ Messaggio di " + longMessage.length() + " caratteri inviato correttamente");
    }

    @Test
    public void testDoGetWithEmptyMessage() throws ServletException, IOException {
        System.out.println("\n=== Test 3: Invio messaggio vuoto ===");

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utenteEmail")).thenReturn("mittente@unisa.it");
        when(request.getParameter("emailInvio")).thenReturn("destinatario@unisa.it");
        when(request.getParameter("testo")).thenReturn("");

        when(accademicoService.trovaEmailUniClass("mittente@unisa.it")).thenReturn(accademicoMittente);
        when(accademicoService.trovaEmailUniClass("destinatario@unisa.it")).thenReturn(accademicoDestinatario);

        Messaggio messaggioVuoto = new Messaggio();
        messaggioVuoto.setBody("");
        messaggioVuoto.setAutore(accademicoMittente);
        messaggioVuoto.setDestinatario(accademicoDestinatario);
        messaggioVuoto.setDateTime(LocalDateTime.now());
        Topic topic = new Topic();
        topic.setNome("VUOTO");
        topic.setCorsoLaurea(corsoLaurea);
        messaggioVuoto.setTopic(topic);

        when(messaggioService.aggiungiMessaggio(any(Messaggio.class))).thenReturn(messaggioVuoto);
        when(messaggioService.trovaTutti()).thenReturn(new ArrayList<>());
        when(messaggioService.trovaMessaggeriDiUnAccademico(anyString())).thenReturn(new ArrayList<>());

        servlet.doGet(request, response);

        ArgumentCaptor<Messaggio> captor = ArgumentCaptor.forClass(Messaggio.class);
        verify(messaggioService).aggiungiMessaggio(captor.capture());
        assertEquals("", captor.getValue().getBody());

        System.out.println("✓ Messaggio vuoto gestito correttamente");
    }

    @Test
    public void testDoGetWithMultipleMessages() throws ServletException, IOException {
        System.out.println("\n=== Test 4: Recupero messaggi multipli ===");

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utenteEmail")).thenReturn("mittente@unisa.it");
        when(request.getParameter("emailInvio")).thenReturn("destinatario@unisa.it");
        when(request.getParameter("testo")).thenReturn("Messaggio di test");

        when(accademicoService.trovaEmailUniClass("mittente@unisa.it")).thenReturn(accademicoMittente);
        when(accademicoService.trovaEmailUniClass("destinatario@unisa.it")).thenReturn(accademicoDestinatario);
        when(messaggioService.aggiungiMessaggio(any(Messaggio.class))).thenReturn(messaggioSalvato);

        // Crea 10 messaggi
        List<Messaggio> messaggi = new ArrayList<>();
        for (int i = 0; i < 10; i++) {
            Messaggio msg = new Messaggio();
            msg.setBody("Messaggio " + i);
            msg.setAutore(accademicoMittente);
            msg.setDestinatario(accademicoDestinatario);
            msg.setDateTime(LocalDateTime.now());
            messaggi.add(msg);
        }
        when(messaggioService.trovaTutti()).thenReturn(messaggi);

        // Crea 5 messaggeri
        List<Accademico> messaggeri = new ArrayList<>();
        for (int i = 0; i < 5; i++) {
            Accademico acc = new Accademico();
            acc.setEmail("utente" + i + "@unisa.it");
            acc.setNome("Nome" + i);
            acc.setCognome("Cognome" + i);
            acc.setMatricola("051210000" + i);
            messaggeri.add(acc);
        }
        when(messaggioService.trovaMessaggeriDiUnAccademico(anyString())).thenReturn(messaggeri);

        servlet.doGet(request, response);

        verify(request).setAttribute("messaggi", messaggi);
        verify(request).setAttribute("accademici", messaggeri);
        assertEquals(10, messaggi.size());
        assertEquals(5, messaggeri.size());

        System.out.println("✓ " + messaggi.size() + " messaggi e " + messaggeri.size() + " messaggeri recuperati");
    }

    @Test
    public void testDoGetWithSpecialCharacters() throws ServletException, IOException {
        System.out.println("\n=== Test 5: Messaggio con caratteri speciali ===");

        String specialMessage = "Messaggio con caratteri speciali: àèéìòù €$£ @#&*() 你好 🎉";

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utenteEmail")).thenReturn("mittente@unisa.it");
        when(request.getParameter("emailInvio")).thenReturn("destinatario@unisa.it");
        when(request.getParameter("testo")).thenReturn(specialMessage);

        when(accademicoService.trovaEmailUniClass("mittente@unisa.it")).thenReturn(accademicoMittente);
        when(accademicoService.trovaEmailUniClass("destinatario@unisa.it")).thenReturn(accademicoDestinatario);

        Messaggio msgSpeciale = new Messaggio();
        msgSpeciale.setBody(specialMessage);
        msgSpeciale.setAutore(accademicoMittente);
        msgSpeciale.setDestinatario(accademicoDestinatario);
        msgSpeciale.setDateTime(LocalDateTime.now());
        Topic topic = new Topic();
        topic.setNome("VUOTO");
        topic.setCorsoLaurea(corsoLaurea);
        msgSpeciale.setTopic(topic);

        when(messaggioService.aggiungiMessaggio(any(Messaggio.class))).thenReturn(msgSpeciale);
        when(messaggioService.trovaTutti()).thenReturn(new ArrayList<>());
        when(messaggioService.trovaMessaggeriDiUnAccademico(anyString())).thenReturn(new ArrayList<>());

        servlet.doGet(request, response);

        ArgumentCaptor<Messaggio> captor = ArgumentCaptor.forClass(Messaggio.class);
        verify(messaggioService).aggiungiMessaggio(captor.capture());
        assertEquals(specialMessage, captor.getValue().getBody());

        System.out.println("✓ Caratteri speciali gestiti correttamente");
    }

    @Test
    public void testDoPost() throws ServletException, IOException {
        System.out.println("\n=== Test 6: Metodo doPost (delega a doGet) ===");

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utenteEmail")).thenReturn("mittente@unisa.it");
        when(request.getParameter("emailInvio")).thenReturn("destinatario@unisa.it");
        when(request.getParameter("testo")).thenReturn("Test doPost");

        when(accademicoService.trovaEmailUniClass("mittente@unisa.it")).thenReturn(accademicoMittente);
        when(accademicoService.trovaEmailUniClass("destinatario@unisa.it")).thenReturn(accademicoDestinatario);
        when(messaggioService.aggiungiMessaggio(any(Messaggio.class))).thenReturn(messaggioSalvato);
        when(messaggioService.trovaTutti()).thenReturn(new ArrayList<>());
        when(messaggioService.trovaMessaggeriDiUnAccademico(anyString())).thenReturn(new ArrayList<>());

        servlet.doPost(request, response);

        // Verifica che doPost chiami effettivamente doGet
        verify(accademicoService).trovaEmailUniClass("mittente@unisa.it");
        verify(accademicoService).trovaEmailUniClass("destinatario@unisa.it");
        verify(messaggioService).aggiungiMessaggio(any(Messaggio.class));
        verify(response).sendRedirect(anyString());

        System.out.println("✓ doPost delega correttamente a doGet");
    }

    @Test
    public void testTopicCreationWithCorsoLaurea() throws ServletException, IOException {
        System.out.println("\n=== Test 7: Creazione Topic con CorsoLaurea ===");

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utenteEmail")).thenReturn("mittente@unisa.it");
        when(request.getParameter("emailInvio")).thenReturn("destinatario@unisa.it");
        when(request.getParameter("testo")).thenReturn("Test topic");

        when(accademicoService.trovaEmailUniClass("mittente@unisa.it")).thenReturn(accademicoMittente);
        when(accademicoService.trovaEmailUniClass("destinatario@unisa.it")).thenReturn(accademicoDestinatario);
        when(messaggioService.aggiungiMessaggio(any(Messaggio.class))).thenReturn(messaggioSalvato);
        when(messaggioService.trovaTutti()).thenReturn(new ArrayList<>());
        when(messaggioService.trovaMessaggeriDiUnAccademico(anyString())).thenReturn(new ArrayList<>());

        servlet.doGet(request, response);

        ArgumentCaptor<Messaggio> captor = ArgumentCaptor.forClass(Messaggio.class);
        verify(messaggioService).aggiungiMessaggio(captor.capture());

        Messaggio messaggio = captor.getValue();
        assertNotNull(messaggio.getTopic());
        assertEquals("VUOTO", messaggio.getTopic().getNome());
        assertEquals(corsoLaurea, messaggio.getTopic().getCorsoLaurea());

        System.out.println("✓ Topic creato correttamente con CorsoLaurea: " + corsoLaurea.getNome());
    }

    @Test
    public void testMessageDateTimeIsSet() throws ServletException, IOException {
        System.out.println("\n=== Test 8: Verifica DateTime del messaggio ===");

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utenteEmail")).thenReturn("mittente@unisa.it");
        when(request.getParameter("emailInvio")).thenReturn("destinatario@unisa.it");
        when(request.getParameter("testo")).thenReturn("Test datetime");

        when(accademicoService.trovaEmailUniClass("mittente@unisa.it")).thenReturn(accademicoMittente);
        when(accademicoService.trovaEmailUniClass("destinatario@unisa.it")).thenReturn(accademicoDestinatario);
        when(messaggioService.aggiungiMessaggio(any(Messaggio.class))).thenReturn(messaggioSalvato);
        when(messaggioService.trovaTutti()).thenReturn(new ArrayList<>());
        when(messaggioService.trovaMessaggeriDiUnAccademico(anyString())).thenReturn(new ArrayList<>());

        LocalDateTime beforeSend = LocalDateTime.now().minusSeconds(1);

        servlet.doGet(request, response);

        LocalDateTime afterSend = LocalDateTime.now().plusSeconds(1);

        ArgumentCaptor<Messaggio> captor = ArgumentCaptor.forClass(Messaggio.class);
        verify(messaggioService).aggiungiMessaggio(captor.capture());

        Messaggio messaggio = captor.getValue();
        assertNotNull(messaggio.getDateTime());
        assertTrue(messaggio.getDateTime().isAfter(beforeSend));
        assertTrue(messaggio.getDateTime().isBefore(afterSend));

        System.out.println("✓ DateTime impostato correttamente: " + messaggio.getDateTime());
    }

    @Test
    public void testRedirectUrlFormat() throws ServletException, IOException {
        System.out.println("\n=== Test 9: Formato URL di redirect ===");

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utenteEmail")).thenReturn("mittente@unisa.it");
        when(request.getParameter("emailInvio")).thenReturn("destinatario@unisa.it");
        when(request.getParameter("testo")).thenReturn("Test redirect");

        when(accademicoService.trovaEmailUniClass("mittente@unisa.it")).thenReturn(accademicoMittente);
        when(accademicoService.trovaEmailUniClass("destinatario@unisa.it")).thenReturn(accademicoDestinatario);
        when(messaggioService.aggiungiMessaggio(any(Messaggio.class))).thenReturn(messaggioSalvato);
        when(messaggioService.trovaTutti()).thenReturn(new ArrayList<>());
        when(messaggioService.trovaMessaggeriDiUnAccademico(anyString())).thenReturn(new ArrayList<>());

        servlet.doGet(request, response);

        ArgumentCaptor<String> urlCaptor = ArgumentCaptor.forClass(String.class);
        verify(response).sendRedirect(urlCaptor.capture());

        String redirectUrl = urlCaptor.getValue();
        assertTrue(redirectUrl.contains("chatServlet"));
        assertTrue(redirectUrl.contains("accademico=destinatario@unisa.it"));
        assertTrue(redirectUrl.contains("accademicoSelf=mittente@unisa.it"));

        System.out.println("✓ URL di redirect corretto: " + redirectUrl);
    }

    @Test
    public void testAllServiceCallsAreMade() throws ServletException, IOException {
        System.out.println("\n=== Test 10: Verifica tutte le chiamate ai service ===");

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utenteEmail")).thenReturn("mittente@unisa.it");
        when(request.getParameter("emailInvio")).thenReturn("destinatario@unisa.it");
        when(request.getParameter("testo")).thenReturn("Test service calls");

        when(accademicoService.trovaEmailUniClass("mittente@unisa.it")).thenReturn(accademicoMittente);
        when(accademicoService.trovaEmailUniClass("destinatario@unisa.it")).thenReturn(accademicoDestinatario);
        when(messaggioService.aggiungiMessaggio(any(Messaggio.class))).thenReturn(messaggioSalvato);
        when(messaggioService.trovaTutti()).thenReturn(new ArrayList<>());
        when(messaggioService.trovaMessaggeriDiUnAccademico(anyString())).thenReturn(new ArrayList<>());

        servlet.doGet(request, response);

        // Verifica tutte le chiamate ai service
        verify(accademicoService, times(1)).trovaEmailUniClass("mittente@unisa.it");
        verify(accademicoService, times(1)).trovaEmailUniClass("destinatario@unisa.it");
        verify(messaggioService, times(1)).aggiungiMessaggio(any(Messaggio.class));
        verify(messaggioService, times(1)).trovaTutti();
        verify(messaggioService, times(1)).trovaMessaggeriDiUnAccademico("0512100001");

        System.out.println("✓ Tutte le chiamate ai service sono state effettuate correttamente");
    }
}

