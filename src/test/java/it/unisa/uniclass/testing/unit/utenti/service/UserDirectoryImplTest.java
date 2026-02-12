package it.unisa.uniclass.testing.unit.utenti.service;

import it.unisa.uniclass.common.exceptions.AuthenticationException;
import it.unisa.uniclass.common.exceptions.NotFoundUserException;
import it.unisa.uniclass.utenti.model.Accademico;
import it.unisa.uniclass.utenti.model.Ruolo;
import it.unisa.uniclass.utenti.model.Utente;
import it.unisa.uniclass.utenti.service.UserDirectoryImpl;
import it.unisa.uniclass.utenti.service.UtenteService;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.InjectMocks;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.Mockito.*;

/**
 * Test Unitario per UserDirectoryImpl.
 *
 */
@ExtendWith(MockitoExtension.class)
class UserDirectoryImplTest {

    @Mock
    private UtenteService utenteService;

    @InjectMocks
    private UserDirectoryImpl userDirectory;

    // --- Login ---

    @Test
    @DisplayName("Login: Delega corretta al service")
    void testLogin() throws AuthenticationException {
        String email = "test@unisa.it";
        String pwd = "pass";
        Utente u = new Utente();

        when(utenteService.login(email, pwd)).thenReturn(u);

        Utente result = userDirectory.login(email, pwd);
        assertSame(u, result);
        verify(utenteService).login(email, pwd);
    }

    // --- Get User (Try/Catch coverage) ---

    @Test
    @DisplayName("GetUser: Successo")
    void testGetUser_Success() throws NotFoundUserException {
        String email = "ok@unisa.it";
        Utente u = new Utente();
        when(utenteService.getUtenteByEmail(email)).thenReturn(u);

        Utente result = userDirectory.getUser(email);
        assertSame(u, result);
    }

    @Test
    @DisplayName("GetUser: Non Trovato (Catch Branch)")
    void testGetUser_NotFound() throws NotFoundUserException {
        String email = "missing@unisa.it";
        when(utenteService.getUtenteByEmail(email)).thenThrow(new NotFoundUserException(""));

        Utente result = userDirectory.getUser(email);
        assertNull(result, "Deve ritornare null se l'eccezione viene catturata");
    }

    // --- Get Accademico (Instanceof coverage) ---

    @Test
    @DisplayName("GetAccademico: Ritorna Accademico se l'utente lo è")
    void testGetAccademico_True() throws NotFoundUserException {
        Accademico acc = new Accademico();
        when(utenteService.getUtenteByEmail("prof@unisa.it")).thenReturn(acc);

        Accademico result = userDirectory.getAccademico("prof@unisa.it");
        assertNotNull(result);
    }

    @Test
    @DisplayName("GetAccademico: Ritorna Null se è un Utente semplice (Else Branch)")
    void testGetAccademico_False() throws NotFoundUserException {
        Utente u = new Utente(); // Non è Accademico
        when(utenteService.getUtenteByEmail("ta@unisa.it")).thenReturn(u);

        Accademico result = userDirectory.getAccademico("ta@unisa.it");
        assertNull(result);
    }

    // --- Controlli Ruolo (Branch Coverage su && e enum) ---

    @Test
    @DisplayName("isDocente: Vero")
    void testIsDocente_True() throws NotFoundUserException {
        Accademico acc = new Accademico();
        acc.setRuolo(Ruolo.DOCENTE);
        when(utenteService.getUtenteByEmail("doc@unisa.it")).thenReturn(acc);

        assertTrue(userDirectory.isDocente("doc@unisa.it"));
    }

    @Test
    @DisplayName("isDocente: Falso (Ruolo errato)")
    void testIsDocente_False_WrongRole() throws NotFoundUserException {
        Accademico acc = new Accademico();
        acc.setRuolo(Ruolo.STUDENTE);
        when(utenteService.getUtenteByEmail("stud@unisa.it")).thenReturn(acc);

        assertFalse(userDirectory.isDocente("stud@unisa.it"));
    }

    @Test
    @DisplayName("isDocente: Falso (Utente null o non accademico)")
    void testIsDocente_False_NotAccademico() throws NotFoundUserException {
        when(utenteService.getUtenteByEmail("null@unisa.it")).thenReturn(null);
        assertFalse(userDirectory.isDocente("null@unisa.it"));
    }

    @Test
    @DisplayName("isStudente: Vero")
    void testIsStudente_True() throws NotFoundUserException {
        Accademico acc = new Accademico();
        acc.setRuolo(Ruolo.STUDENTE);
        when(utenteService.getUtenteByEmail("s@unisa.it")).thenReturn(acc);

        assertTrue(userDirectory.isStudente("s@unisa.it"));
    }

    @Test
    @DisplayName("isCoordinatore: Vero")
    void testIsCoordinatore_True() throws NotFoundUserException {
        Accademico acc = new Accademico();
        acc.setRuolo(Ruolo.COORDINATORE);
        when(utenteService.getUtenteByEmail("c@unisa.it")).thenReturn(acc);

        assertTrue(userDirectory.isCoordinatore("c@unisa.it"));
    }

    // --- Liste ---

    @Test
    @DisplayName("Get Tutti Gli Utenti")
    void testGetTuttiGliUtenti() {
        userDirectory.getTuttiGliUtenti();
        verify(utenteService).getTuttiGliUtenti();
    }

    @Test
    @DisplayName("Get Accademici Per Ruolo")
    void testGetAccademiciPerRuolo() {
        userDirectory.getAccademiciPerRuolo(Ruolo.DOCENTE);
        verify(utenteService).getAccademiciPerRuolo(Ruolo.DOCENTE);
    }

    // --- Aggiornamenti ---

    @Test
    @DisplayName("Update Profile")
    void testUpdateProfile() {
        Utente u = new Utente();
        userDirectory.updateProfile(u);
        verify(utenteService).aggiornaUtente(u);
    }

    @Test
    @DisplayName("Cambia Stato Attivazione: Esegui su Accademico (If Branch)")
    void testCambiaStatoAttivazione_Accademico() throws NotFoundUserException {
        Accademico acc = new Accademico();
        acc.setAttivato(false); // Stato iniziale

        when(utenteService.getUtenteByEmail("acc@unisa.it")).thenReturn(acc);

        userDirectory.cambiaStatoAttivazione("acc@unisa.it", true);

        assertTrue(acc.isAttivato(), "Lo stato dell'oggetto dovrebbe essere cambiato a true");
        verify(utenteService).aggiornaUtente(acc);
    }

    @Test
    @DisplayName("Cambia Stato Attivazione: Ignora non Accademico (Else Branch)")
    void testCambiaStatoAttivazione_Ignored() throws NotFoundUserException {
        Utente u = new Utente(); // Non accademico
        when(utenteService.getUtenteByEmail("user@unisa.it")).thenReturn(u);

        userDirectory.cambiaStatoAttivazione("user@unisa.it", true);

        // Verifica che NON venga chiamato l'update
        verify(utenteService, never()).aggiornaUtente(any());
    }
}