package it.unisa.uniclass.testing.unit.conversazioni.controller;

import it.unisa.uniclass.conversazioni.controller.inviaMessaggioChatServlet;
import it.unisa.uniclass.conversazioni.model.Messaggio;
import it.unisa.uniclass.conversazioni.model.Topic;
import it.unisa.uniclass.conversazioni.service.MessaggioService;
import it.unisa.uniclass.orari.model.CorsoLaurea;
import it.unisa.uniclass.utenti.model.Accademico;
import it.unisa.uniclass.utenti.service.UserDirectory;
import jakarta.servlet.ServletContext;
import jakarta.servlet.ServletException;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import java.io.IOException;
import java.lang.reflect.Field;
import java.util.ArrayList;
import java.util.List;

import static org.mockito.ArgumentMatchers.any;
import static org.mockito.Mockito.*;

@ExtendWith(MockitoExtension.class)
class inviaMessaggioChatServletTest {

    private inviaMessaggioChatServlet servlet;

    @Mock private HttpServletRequest request;
    @Mock private HttpServletResponse response;
    @Mock private HttpSession session;
    @Mock private ServletContext servletContext;
    @Mock private MessaggioService messaggioService;
    @Mock private UserDirectory userDirectory;

    @BeforeEach
    void setUp() throws Exception {
        servlet = new inviaMessaggioChatServlet();

        // Inject EJB MessaggioService
        Field msgServiceField = inviaMessaggioChatServlet.class.getDeclaredField("messaggioService");
        msgServiceField.setAccessible(true);
        msgServiceField.set(servlet, messaggioService);

        // Inject EJB UserDirectory
        Field userServiceField = inviaMessaggioChatServlet.class.getDeclaredField("userDirectory");
        userServiceField.setAccessible(true);
        userServiceField.set(servlet, userDirectory);

        // Common Mocks
        lenient().when(request.getSession()).thenReturn(session);
        lenient().when(request.getServletContext()).thenReturn(servletContext);
    }

    @Test
    @DisplayName("DoGet: Successo - Utenti validi e messaggio inviato")
    void testDoGet_Success() throws IOException {
        // Arrange
        String emailSelf = "me@unisa.it";
        String emailDest = "dest@unisa.it";
        String testo = "Ciao!";

        when(session.getAttribute("utenteEmail")).thenReturn(emailSelf);
        when(request.getParameter("emailInvio")).thenReturn(emailDest);
        when(request.getParameter("testo")).thenReturn(testo);

        Accademico sender = mock(Accademico.class);
        Accademico receiver = mock(Accademico.class);
        CorsoLaurea cl = new CorsoLaurea();

        when(sender.getEmail()).thenReturn(emailSelf);
        when(sender.getCorsoLaurea()).thenReturn(cl); // Serve per new Topic()
        when(receiver.getEmail()).thenReturn(emailDest);

        when(userDirectory.getAccademico(emailSelf)).thenReturn(sender);
        when(userDirectory.getAccademico(emailDest)).thenReturn(receiver);

        // Preparazione lista per copertura loop lazy loading
        List<Messaggio> listaMessaggi = new ArrayList<>();
        Messaggio m = new Messaggio();
        m.setAutore(sender);
        m.setDestinatario(receiver);
        m.setTopic(new Topic());
        listaMessaggi.add(m);

        when(messaggioService.trovaTutti()).thenReturn(listaMessaggi);

        // Act
        servlet.doGet(request, response);

        // Assert
        verify(messaggioService).aggiungiMessaggio(any(Messaggio.class));
        verify(response).sendRedirect(contains("chatServlet?accademico=" + emailDest));

        // Verifica chiamate lazy loading (Branch coverage)
        verify(sender, atLeastOnce()).getNome();
        verify(receiver, atLeastOnce()).getNome();
    }

    @Test
    @DisplayName("DoGet: Fallimento - Uno degli utenti non esiste (Exception Branch)")
    void testDoGet_UsersNotFound() throws IOException {
        // Arrange
        when(session.getAttribute("utenteEmail")).thenReturn("me@unisa.it");
        when(request.getParameter("emailInvio")).thenReturn("missing@unisa.it");

        when(userDirectory.getAccademico("me@unisa.it")).thenReturn(new Accademico());
        when(userDirectory.getAccademico("missing@unisa.it")).thenReturn(null); // Destinatario mancante

        // Act
        servlet.doGet(request, response);

        // Assert
        // Il servlet lancia ServletException nel try, catturata e loggata
        verify(messaggioService, never()).aggiungiMessaggio(any());
        verify(response).sendError(HttpServletResponse.SC_INTERNAL_SERVER_ERROR);
        verify(servletContext).log(eq("Error processing chat message"), any(ServletException.class));
    }

    @Test
    @DisplayName("DoPost: Delega a DoGet")
    void testDoPost() throws ServletException, IOException {
        // Setup minimo per evitare NPE prima della delega
        when(request.getSession()).thenReturn(session);
        // Forziamo un errore subito per verificare che doPost chiami doGet
        when(userDirectory.getAccademico(any())).thenThrow(new RuntimeException("Delega OK"));

        servlet.doPost(request, response);

        verify(servletContext).log(eq("Error processing chat message"), any(RuntimeException.class));
    }
}